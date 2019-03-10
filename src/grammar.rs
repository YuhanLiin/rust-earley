#[macro_export]
macro_rules! grammar {
    ( @rules $grammar:ident, ) => ();

    ( @rules $grammar:ident, $lhs:ident = [ $($rhs:tt)* ]
      $( $tail:tt )* ) => (
        grammar!(@rhs $grammar, $lhs, $($rhs)*);
        //
        // Detects recursive grammars with no base case and aborts if found
        assert!($grammar.is_nullable($lhs) ||
                $grammar.get_iter_rhs($lhs).map(|rule|
                    rule.iter().all(|sym| match sym {
                        __inner::Symbol::Terminal(_) => true,
                        __inner::Symbol::NonTerminal(nt) => *nt != $lhs,
                    })
                ).any(|b| b));

        grammar!(@rules $grammar, $($tail)*);
    );

    ( @rhs $grammar:ident, $lhs:ident, ) => (
        $grammar.set_nullable($lhs);
    );

    ( @rhs $grammar:ident, $lhs:ident, $($symbol:ident)* $( | $($tail:tt)* )? ) => (
        $grammar.add_rule($lhs, vec![ $(__inner::Symbol::new($symbol)),* ]);
        grammar!(@rhs_tail $grammar, $lhs, $(| $($tail)*)?)
    );

    ( @rhs_tail $grammar:ident, $lhs:ident, ) => ();

    ( @rhs_tail $grammar:ident, $lhs:ident, | $( $tail:tt )* ) => (
        grammar!(@rhs $grammar, $lhs, $($tail)*)
    );

    ( $name:ident <$Token:path>:
      $( $lhs:ident = $rhs:tt )* ) => (

    #[allow(unused)]
    mod $name {
        #[allow(unused)]
        mod __inner {
            use std::collections::HashMap;
            use std::iter;

            #[derive(Debug)]
            #[derive(Hash, PartialEq, Eq, Clone, Copy)]
            pub enum NonTerminal {
                $($lhs,)*
                __NonTerminalEnd,
            }

            pub const NT_COUNT: usize = NonTerminal::__NonTerminalEnd as usize;

            #[derive(Debug)]
            #[derive(PartialEq, Eq)]
            pub enum Symbol{
                Terminal($Token),
                NonTerminal(NonTerminal),
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

            #[derive(Debug)]
            pub struct Rule(Vec<Symbol>);

            impl Rule {
                pub fn iter(&self) -> impl Iterator<Item=&Symbol> {
                    self.0.iter()
                }

                pub fn len(&self) -> usize { self.0.len() }

                pub fn symbol(&self, i: usize) -> Option<&Symbol> { self.0.get(i) }
            }

            #[derive(Debug)]
            pub struct Grammar {
                rules: HashMap<NonTerminal, Vec<Rule>>,
                nullable: [bool; NT_COUNT],
            }

            impl Grammar {
                pub(super) fn new() -> Self {
                    Grammar {
                        rules: HashMap::new(),
                        nullable: [false; NT_COUNT],
                    }
                }

                pub(super) fn add_rule(&mut self, lhs: NonTerminal, rhs: Vec<Symbol>) {
                    let prod_rules = self.rules.entry(lhs).or_insert(Vec::new());
                    prod_rules.push(Rule(rhs));
                }

                pub(super) fn set_nullable(&mut self, sym: NonTerminal) {
                    self.nullable[sym as usize] = true;
                }

                pub(super) fn compute_nullable(&mut self) {
                    let mut rhs_mapping: [Vec<(NonTerminal, &Rule)>; NT_COUNT] = Default::default();

                    let rules = self.iter_lhs().map(|l| *l).filter(|lhs| !self.is_nullable(*lhs)).flat_map(|lhs| {
                        iter::repeat(lhs).zip(self.get_iter_rhs(lhs))
                    });

                    for (lhs, rule) in rules {
                        for sym in rule.iter() {
                            if let Symbol::NonTerminal(nt) = sym {
                                rhs_mapping[*nt as usize].push((lhs, rule));
                            } else {
                                break;
                            }
                        }
                    }

                    let mut work_symbols = self.iter_lhs().map(|l| *l)
                                                       .filter(|l| self.is_nullable(*l))
                                                       .collect::<Vec<NonTerminal>>();
                    let mut nullable = self.nullable.clone();

                    while !work_symbols.is_empty() {
                        let sym = work_symbols.pop().unwrap();

                        for (lhs, rule) in rhs_mapping[sym as usize].iter() {
                            if !nullable[*lhs as usize] {
                                if rule.iter().all(|sym| match sym {
                                    Symbol::NonTerminal(nt) => nullable[*nt as usize],
                                    _ => false
                                }) {
                                    nullable[*lhs as usize] = true;
                                    work_symbols.push(*lhs);
                                }
                            }
                        }
                    }

                    self.nullable = nullable.clone();
                }

                pub fn get_iter_rhs(
                    &self,
                    lhs: NonTerminal
                ) -> impl Iterator<Item=&Rule>
                {
                    self.rules.get(&lhs).into_iter().flat_map(|vec| vec.iter())
                }

                pub fn iter_lhs(&self) -> impl Iterator<Item=&NonTerminal> {
                    static NONTERMINALS: [NonTerminal; NT_COUNT] = [$(NonTerminal::$lhs),*];
                    NONTERMINALS.iter()
                }

                pub fn is_nullable(&self, non_term: NonTerminal) -> bool {
                    self.nullable[non_term as usize]
                }
            }

        }

        use __inner::MakeSymbol;

        pub fn get_grammar() -> __inner::Grammar {
            use $Token::*;
            use __inner::NonTerminal::*;

            let mut __grammar = __inner::Grammar::new();
            grammar!(@rules __grammar, $( $lhs = $rhs )*);
            __grammar.compute_nullable();
            __grammar
        }

        pub use __inner::{Grammar, Rule, Symbol, NonTerminal, NT_COUNT};
        pub use $Token;
    }
    )
}

#[cfg(test)]
mod tests {
    use std::iter::FromIterator;

    #[derive(Debug, PartialEq, Eq)]
    pub enum Tok {
        NUM,
        PLUS,
        MINUS,
    }

    // Just testing if this invocation even compiles
    grammar!(name_clash <crate::grammar::tests::Tok>:
             Symbol = [Rule]
             Rule = [NonTerminal]
             NonTerminal = [Rule]
             Tok = [Symbol]
             Grammar = [Tok]
             grammar = [grammar]
             get_grammar = []);

    grammar!(empty_grammar <crate::grammar::tests::Tok>:);

    grammar!(test_grammar <crate::grammar::tests::Tok>:
             Empty = []
             Stmt = [Expr | ]
             Expr = [NUM | Expr PLUS Expr | Expr MINUS Expr]
    );

    #[test]
    fn empty() {
        use empty_grammar::*;

        let grammar = get_grammar();

        assert_eq!(grammar.iter_lhs().count(), 0);
    }

    #[test]
    fn grammar() {
        use test_grammar::*;

        let grammar = get_grammar();

        let rules = Vec::from_iter(grammar.get_iter_rhs(NonTerminal::Empty));
        assert_eq!(rules.len(), 0);
        assert!(grammar.is_nullable(NonTerminal::Empty));

        let rules = Vec::from_iter(grammar.get_iter_rhs(NonTerminal::Stmt));
        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0].len(), 1);
        assert_eq!(
            rules[0].symbol(0).unwrap(),
            &Symbol::NonTerminal(NonTerminal::Expr)
        );
        assert!(grammar.is_nullable(NonTerminal::Stmt));

        let rules = Vec::from_iter(grammar.get_iter_rhs(NonTerminal::Expr));
        assert_eq!(rules.len(), 3);
        let rules = Vec::from_iter(rules.iter().map(|rule| Vec::from_iter(rule.iter())));
        assert_eq!(rules[0], vec![&Symbol::Terminal(Tok::NUM)]);
        assert_eq!(
            rules[1],
            vec![
                &Symbol::NonTerminal(NonTerminal::Expr),
                &Symbol::Terminal(Tok::PLUS),
                &Symbol::NonTerminal(NonTerminal::Expr),
            ]
        );
        assert_eq!(
            rules[2],
            vec![
                &Symbol::NonTerminal(NonTerminal::Expr),
                &Symbol::Terminal(Tok::MINUS),
                &Symbol::NonTerminal(NonTerminal::Expr),
            ]
        );
    }

    grammar!(nullable_grammar <crate::grammar::tests::Tok>:
             A = []
             B = [A]
             C = [B A | NUM]
             D = [PLUS | C NUM B]
             E = [C D]
             F = [A B C | E]);

    #[test]
    fn nullable() {
        use nullable_grammar::*;

        let grammar = get_grammar();

        assert!(grammar.is_nullable(NonTerminal::A));
        assert!(grammar.is_nullable(NonTerminal::B));
        assert!(grammar.is_nullable(NonTerminal::C));
        assert!(!grammar.is_nullable(NonTerminal::D));
        assert!(!grammar.is_nullable(NonTerminal::E));
        assert!(grammar.is_nullable(NonTerminal::F));
    }
}
