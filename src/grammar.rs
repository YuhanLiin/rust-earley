pub trait Rule<'a> {
    type Symbol: 'a;
    type SymIter: Iterator<Item=&'a Self::Symbol>;

    fn iter(&'a self) -> Self::SymIter;

    fn len(&'a self) -> usize;

    fn symbol(&'a self, i: usize) -> Option<&Self::Symbol>;
}

pub trait Grammar<'a> {
    type NonTerminal: 'a;
    type NonTermIter: Iterator<Item=&'a Self::NonTerminal>;
    type Rule: 'a;
    type RuleIter: Iterator<Item=&'a Self::Rule>;

    fn get_iter_rhs(&'a self, lhs: &Self::NonTerminal) -> Self::RuleIter;

    fn iter_lhs(&'a self) -> Self::NonTermIter;

    fn is_nullable(&'a self, non_term: &Self::NonTerminal) -> bool; 
}

pub trait Symbol {
    type NonTerminal;
    type Terminal;

    fn terminal(&self) -> Option<&Self::Terminal>;

    fn nonterminal(&self) -> Option<&Self::NonTerminal>;

    fn call_match<FN, FT>(&self, nt_handler: FN, t_handler: FT)
    where FN: FnOnce(&Self::NonTerminal), FT: FnOnce(&Self::Terminal);
}

pub trait NonTerminal {
    const count: usize;

    fn to_usize(&self) -> usize;
}

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
            #[derive(Hash, PartialEq, Eq, Clone, Copy)]
            pub enum NonTerminal {
                $($lhs,)*
                __NonTerminalEnd,
            }

            const NT_COUNT: usize = __NonTerminalEnd as usize;

            impl $crate::grammar::NonTerminal for NonTerminal {
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

            impl $crate::grammar::Symbol for Symbol {
                type Terminal = $Token;
                type NonTerminal = NonTerminal;

                fn terminal(&self) -> Option<&Self::Terminal> {
                    if let Symbol::Terminal(t) = self {
                        Some(&t)
                    } else { None }
                }

                fn nonterminal(&self) -> Option<&Self::NonTerminal> {
                    if let Symbol::NonTerminal(t) = self {
                        Some(&t)
                    } else { None }
                }

                fn call_match<FN, FT>(&self, nt_handler: FN, t_handler: FT)
                where FN: FnOnce(&Self::NonTerminal), FT: FnOnce(&Self::Terminal)
                {
                    match self {
                        Symbol::Terminal(t) => t_handler(t),
                        Symbol::NonTerminal(nt) => nt_handler(nt),
                    }
                }
            }

            trait MakeSymbol<T> {
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

            impl<'a> $crate::grammar::Rule<'a> for Rule {
                type Symbol = Symbol;
                type SymIter = std::slice::Iter<'a, Symbol>;

                fn iter(&'a self) -> Self::SymIter {
                    self.0.iter()
                }

                fn len(&self) -> usize { self.0.len() }

                fn symbol(&self, i: usize) -> Option<&Symbol> { self.0.get(i) }
            }

            pub struct Grammar {
                rules: std::collections::HashMap<NonTerminal, Vec<Rule>>,
                nullable: [bool; NT_COUNT],
            }

            impl Grammar {
                fn new() -> Self {
                    Grammar {
                        rules: std::collections::HashMap::new(),
                        nullable: [false; NT_COUNT],
                    }
                }

                fn add_rule(&mut self, lhs: NonTerminal, rhs: Vec<Symbol>) {
                    let prod_rules = self.rules.entry(lhs).or_insert(Vec::new());
                    prod_rules.push(Rule(rhs));
                }
            }

            impl<'a> $crate::grammar::Grammar<'a> for Grammar {
                type NonTerminal = NonTerminal;
                type NonTermIter =
                    std::collections::hash_map::Keys<'a, NonTerminal, Vec<Rule>>;
                type Rule = Rule;
                type RuleIter = std::slice::Iter<'a, Rule>;

                fn get_iter_rhs(&'a self, lhs: &Self::NonTerminal)
                -> Self::RuleIter
                {
                    self.rules.get(lhs).map(|vec| vec.iter()).unwrap()
                }

                fn iter_lhs(&'a self) -> Self::NonTermIter {
                    self.rules.keys()
                }

                fn is_nullable(&'a self, non_term: &Self::NonTerminal) -> bool {
                    false
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
    use super::*;

    #[derive(Debug)]
    #[derive(PartialEq)]
    #[derive(Eq)]
    pub enum Tok {
        NUM, PLUS, MINUS,
    }

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
