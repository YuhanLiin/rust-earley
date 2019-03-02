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

    ( $name:ident, $Token:path,
      $( $lhs:ident = $rhs:tt )* ) => (

        mod $name {
            use std::collections::HashMap;

            #[derive(Debug)]
            #[derive(PartialEq)]
            #[derive(Eq)]
            #[derive(Hash)]
            pub enum NonTerminal {
                $($lhs),*
            }

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

                pub fn len(&self) -> usize {
                    self.0.len()
                }
            }

            pub struct Grammar {
                rules: HashMap<NonTerminal, Vec<Rule>>,
            }

            impl Grammar {
                fn new() -> Self {
                    Grammar { rules: HashMap::new() }
                }

                fn add_rule(&mut self, lhs: NonTerminal, rhs: Vec<Symbol>) {
                    let prod_rules = self.rules.entry(lhs).or_insert(Vec::new());
                    prod_rules.push(Rule(rhs));
                }

                pub fn iter_rhs<T>(&self, lhs: &NonTerminal)
                -> Option<impl Iterator<Item=&Rule>>
                {
                    self.rules.get(lhs).map(|vec| vec.iter())
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

    enum Tok {
        NUM, PLUS, MINUS,
    }

    grammar!(TestGrammar, crate::tests::Tok,
             empty = []
             stmt = [expr | ]
             expr = [NUM | expr PLUS expr | expr MINUS expr]
    );

    #[test]
    fn it_works() {
        use crate::tests::TestGrammar::*;

        let grammar = get_grammar();

        let non_terminals: HashSet<&NonTerminal> =
            HashSet::from_iter(grammar.iter_lhs());
        assert!(non_terminals.get(&NonTerminal::empty).is_some());
        assert!(non_terminals.get(&NonTerminal::stmt).is_some());
        assert!(non_terminals.get(&NonTerminal::expr).is_some());
    }
}
