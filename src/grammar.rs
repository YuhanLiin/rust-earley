#[macro_export]
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
        $grammar.add_rule($lhs, vec![ $(_Inner::Symbol::new($symbol)),* ]);
        grammar!(@rhs_tail $grammar, $lhs, $(| $($tail)*)?)
    );

    ( @rhs_tail $grammar:ident, $lhs:ident, ) => ();

    ( @rhs_tail $grammar:ident, $lhs:ident, | $( $tail:tt )* ) => (
        $grammar!(@rhs $grammar, $lhs, $($tail)*)
    );

    ( $name:ident <$Token:path>:
      $( $lhs:ident = $rhs:tt )* ) => (

        mod $name {
            mod _Inner {
                #[derive(Debug)]
                #[derive(Hash, PartialEq, Eq, Clone, Copy)]
                pub enum NonTerminal {
                    $($lhs,)*
                    __NonTerminalEnd,
                }

                const NT_COUNT: usize = NonTerminal::__NonTerminalEnd as usize;

                impl NonTerminal {
                    const count: usize = NT_COUNT;

                    fn to_usize(&self) -> usize {
                        *self as usize
                    }
                }

                #[derive(Debug)]
                #[derive(PartialEq, Eq)]
                pub enum Symbol{
                    Terminal($Token),
                    NonTerminal(NonTerminal),
                }

                impl Symbol {
                    pub fn terminal(&self) -> Option<&$Token> {
                        if let Symbol::Terminal(t) = self {
                            Some(&t)
                        } else { None }
                    }

                    pub fn nonterminal(&self) -> Option<&NonTerminal> {
                        if let Symbol::NonTerminal(t) = self {
                            Some(&t)
                        } else { None }
                    }

                    pub fn call_match<FN, FT>(&self, nt_handler: FN, t_handler: FT)
                        where FN: FnOnce(&NonTerminal),
                              FT: FnOnce(&$Token)
                        {
                            match self {
                                Symbol::Terminal(t) => t_handler(t),
                                Symbol::NonTerminal(nt) => nt_handler(nt),
                            }
                        }
                }

                pub trait MakeSymbol<T> {
                    fn new(arg: T) -> Self;
                }

                // Allows static dispatch on new()
                impl MakeSymbol<NonTerminal> for Symbol {
                    fn new(arg: NonTerminal) -> Self {
                        Symbol::NonTerminal(arg)
                    }
                }
                impl MakeSymbol<$Token> for Symbol {
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

                    pub fn symbol(&self, i: usize) -> Option<&Symbol> { self.0.get(i) }
                }

                pub struct Grammar {
                    rules: std::collections::HashMap<NonTerminal, Vec<Rule>>,
                    nullable: [bool; NT_COUNT],
                }

                impl Grammar {
                    pub fn new() -> Self {
                        Grammar {
                            rules: std::collections::HashMap::new(),
                            nullable: [false; NT_COUNT],
                        }
                    }

                    pub fn add_rule(&mut self, lhs: NonTerminal, rhs: Vec<Symbol>) {
                        let prod_rules = self.rules.entry(lhs).or_insert(Vec::new());
                        prod_rules.push(Rule(rhs));
                    }

                    pub fn get_iter_rhs(
                        &self,
                        lhs: &NonTerminal
                    ) -> impl Iterator<Item=&Rule>
                    {
                        self.rules.get(lhs).map(|vec| vec.iter()).unwrap()
                    }

                    pub fn iter_lhs(&self) -> impl Iterator<Item=&NonTerminal> {
                        self.rules.keys()
                    }

                    pub fn is_nullable(&self, non_term: &NonTerminal) -> bool {
                        false
                    }
                }
            }

            use $Token::*;
            use _Inner::NonTerminal::*;
            use _Inner::MakeSymbol;

            pub fn get_grammar() -> _Inner::Grammar {
                let mut grammar = _Inner::Grammar::new();
                grammar!(@rules grammar, $( $lhs = $rhs )*);
                grammar
            }

            pub use _Inner::{Grammar, Rule, Symbol, NonTerminal};
            pub use $Token;
        }
    )
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::iter::FromIterator;
    use super::*;

    #[derive(Debug)]
    #[derive(PartialEq)]
    #[derive(Eq)]
    pub enum Tok {
        NUM, PLUS, MINUS,
    }

    // Just testing if this invocation even compiles
    grammar!(NameClash <crate::grammar::tests::Tok>:
             Symbol = [Rule]
             Rule = [NonTerminal]
             NonTerminal = [Rule]
             Tok = [Symbol]
             Grammar = [Tok]);

    grammar!(EmptyGrammar <crate::grammar::tests::Tok>:);

    grammar!(TestGrammar <crate::grammar::tests::Tok>:
             empty = []
             stmt = [expr | ]
             expr = [NUM | expr PLUS expr | expr MINUS expr]
    );

    #[test]
    fn empty() {
        use EmptyGrammar::*;

        let grammar = get_grammar();

        assert_eq!(grammar.iter_lhs().count(), 0);
    }

    #[test]
    fn grammar() {
        use TestGrammar::*;

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
        assert_eq!(
            rules[0].symbol(0).unwrap(),
            &Symbol::NonTerminal(NonTerminal::expr)
        );
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
