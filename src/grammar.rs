macro_rules! grammar {
    ( @rules $grammar:ident, ) => ();

    ( @rules $grammar:ident, $lhs:ident = [ $($rhs:tt)* ]
      $( $tail:tt )* ) => (
        $grammar!(@rhs $grammar, $lhs, $($rhs)*);
        grammar!(@rules $grammar, $($tail)*)
    );

    ( @rhs $grammar:ident, $lhs:ident, ) => (
        $grammar.add_rule($lhs, vec![]);
    );

    ( @rhs $grammar:ident, $lhs:ident, $($symbol:ident)* $( | $($tail:tt)* )? ) => (
        $grammar.add_rule($lhs, vec![ $(Symbol::new($symbol)),* ]);
        grammar!(@rhs_tail $grammar, $lhs, $(| $($tail)*)?)
    );

    ( @rhs_tail $grammar:ident, $lhs:ident, ) => ();

    ( @rhs_tail $grammar:ident, $lhs:ident, | $( $tail:tt )* ) => (
        $grammar!(@rhs $grammar, $lhs, $($tail)*)
    );

    ( $name:ident <$Token:path>:
      $( $lhs:ident = $rhs:tt )* ) => (

        mod $name {
            #[derive(Debug)]
            #[derive(PartialEq)]
            #[derive(Eq)]
            #[derive(Hash)]
            pub enum NonTerminal {
                $($lhs),*
            }

            #[derive(Debug)]
            #[derive(PartialEq)]
            #[derive(Eq)]
            pub enum Symbol{
                Terminal($Token),
                NonTerminal(NonTerminal),
            }

            trait mk_symbol<T> {
                fn new(arg: T) -> Self;
            }

            impl mk_symbol<NonTerminal> for Symbol {
                fn new(arg: NonTerminal) -> Self {
                    Symbol::NonTerminal(arg)
                }
            }
            impl mk_symbol<$Token> for Symbol {
                fn new(arg: $Token) -> Self {
                    Symbol::Terminal(arg)
                }
            }

            pub struct Rule(Vec<Symbol>);

            impl Rule {
                pub fn iter(&self) -> impl Iterator<Item=&Symbol> {
                    self.0.iter()
                }

                pub fn len(&self) -> usize { self.0.len() }


                pub fn symbol(&self, i: usize) -> &Symbol { &self.0[i] }
            }

            pub struct Grammar {
                rules: std::collections::HashMap<NonTerminal, Vec<Rule>>,
            }

            impl Grammar {
                fn new() -> Self {
                    Grammar { rules: std::collections::HashMap::new() }
                }

                fn add_rule(&mut self, lhs: NonTerminal, rhs: Vec<Symbol>) {
                    let prod_rules = self.rules.entry(lhs).or_insert(Vec::new());
                    prod_rules.push(Rule(rhs));
                }

                pub fn get_iter_rhs(&self, lhs: &NonTerminal)
                -> impl Iterator<Item=&Rule>
                {
                    self.rules.get(lhs).map(|vec| vec.iter()).unwrap()
                }

                pub fn iter_lhs(&self) -> impl Iterator<Item=&NonTerminal> {
                    self.rules.keys()
                }
            }

            use $Token::*;
            use NonTerminal::*;

            pub fn get_grammar() -> Grammar {
                let mut grammar = Grammar::new();
                grammar!(@rules grammar, $( $lhs = $rhs )*);
                grammar
            }

        }
    )
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::iter::FromIterator;

    #[derive(Debug)]
    #[derive(PartialEq)]
    #[derive(Eq)]
    enum Tok {
        NUM, PLUS, MINUS,
    }

    grammar!(EmptyGrammar <crate::tests::Tok>:);

    grammar!(TestGrammar <crate::tests::Tok>:
             empty = []
             stmt = [expr | ]
             expr = [NUM | expr PLUS expr | expr MINUS expr]
    );

    #[test]
    fn empty() {
        use crate::tests::EmptyGrammar::*;

        let grammar = get_grammar();

        assert_eq!(grammar.iter_lhs().count(), 0);
    }

    #[test]
    fn grammar() {
        use crate::tests::TestGrammar::*;

        let grammar = get_grammar();

        let non_terminals: HashSet<&NonTerminal> =
            HashSet::from_iter(grammar.iter_lhs());

        let rules =
            Vec::from_iter(grammar.get_iter_rhs(&NonTerminal::empty));
        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0].len(), 0);

        let rules =
            Vec::from_iter(grammar.get_iter_rhs(&NonTerminal::stmt));
        assert_eq!(rules.len(), 2);
        assert_eq!(rules[0].len(), 1);
        assert_eq!(rules[0].symbol(0), &Symbol::NonTerminal(NonTerminal::expr));
        assert_eq!(rules[1].len(), 0);

        let rules =
            Vec::from_iter(grammar.get_iter_rhs(&NonTerminal::expr));
        assert_eq!(rules.len(), 3);
        let rules = Vec::from_iter(rules.iter().map(|rule| {
            Vec::from_iter(rule.iter())
        }));
        assert_eq!(rules[0], vec![&Symbol::Terminal(Tok::NUM)]);
        assert_eq!(rules[1], vec![
            &Symbol::NonTerminal(NonTerminal::expr),
            &Symbol::Terminal(Tok::PLUS),
            &Symbol::NonTerminal(NonTerminal::expr),
        ]);
        assert_eq!(rules[2], vec![
            &Symbol::NonTerminal(NonTerminal::expr),
            &Symbol::Terminal(Tok::MINUS),
            &Symbol::NonTerminal(NonTerminal::expr),
        ]);
    }
}
