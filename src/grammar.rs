#[macro_export]
macro_rules! grammar {
    ( @rules $grammar:ident, ) => ();

    ( @rules $grammar:ident, $lhs:ident = [ $($rhs:tt)* ]
      $( $tail:tt )* ) => (
        grammar!(@rhs $grammar, $lhs, $($rhs)*);
        grammar!(@rules $grammar, $($tail)*);
    );

    ( @rhs_rule $grammar:ident, $lhs:ident, ) => (
        $grammar.set_nullable($lhs);
    );

    ( @rhs_rule $grammar:ident, $lhs:ident, $($symbol:ident)+) => (
        $grammar.add_rule($lhs, vec![ $(__inner::Symbol::new($symbol)),* ]);
    );

    ( @rhs $grammar:ident, $lhs:ident, $($symbol:ident)* $( | $($tail:tt)* )? ) => (
        grammar!(@rhs_rule $grammar, $lhs, $($symbol)*);
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

            impl Symbol {
                pub fn terminal(&self) -> $Token {
                    match self {
                        Symbol::Terminal(t) => t.clone(),
                        _ => panic!("Expected symbol to be terminal")
                    }
                }

                pub fn non_terminal(&self) -> NonTerminal {
                    match self {
                        Symbol::NonTerminal(nt) => nt.clone(),
                        _ => panic!("Expected symbol to be nonterminal")
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

            #[derive(Debug)]
            pub struct Rule(Vec<Symbol>);

            impl Rule {
                pub fn iter(&self) -> impl DoubleEndedIterator<Item=&Symbol> {
                    self.0.iter()
                }

                pub fn len(&self) -> usize { self.0.len() }

                pub fn symbol(&self, i: usize) -> Option<&Symbol> { self.0.get(i) }
            }

            #[derive(Debug)]
            struct GrammarRules(HashMap<NonTerminal, Vec<Rule>>);

            impl GrammarRules {
                fn add_rule(&mut self, lhs: NonTerminal, rhs: Vec<Symbol>) {
                    let prod_rules = self.0.entry(lhs).or_insert(Vec::new());
                    prod_rules.push(Rule(rhs));
                }

                fn get_iter_rhs(
                    &self,
                    lhs: NonTerminal
                ) -> impl Iterator<Item=&Rule>
                {
                    self.0.get(&lhs).into_iter().flat_map(|vec| vec.iter())
                }
            }

            #[derive(Debug)]
            pub struct Grammar {
                rules: GrammarRules,
                nullable: [bool; NT_COUNT],
            }

            impl Grammar {
                pub(super) fn new() -> Self {
                    Grammar {
                        rules: GrammarRules(HashMap::new()),
                        nullable: [false; NT_COUNT],
                    }
                }

                pub(super) fn add_rule(&mut self, lhs: NonTerminal, rhs: Vec<Symbol>) {
                    self.rules.add_rule(lhs, rhs);
                }

                pub(super) fn set_nullable(&mut self, sym: NonTerminal) {
                    self.nullable[sym as usize] = true;
                }

                pub(super) fn compute_nullable(&mut self) {
                    let mut rhs_mapping: [Vec<(NonTerminal, &Rule)>; NT_COUNT] = Default::default();

                    let rules = &self.rules;
                    let rules_iter = self.iter_lhs()
                                         .map(|l| *l)
                                         .filter(|lhs| !self.is_nullable(*lhs))
                                         .flat_map(|lhs| iter::repeat(lhs).zip(rules.get_iter_rhs(lhs)));

                    for (lhs, rule) in rules_iter {
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

                    while !work_symbols.is_empty() {
                        let sym = work_symbols.pop().unwrap();

                        for (lhs, rule) in rhs_mapping[sym as usize].iter() {
                            if !self.is_nullable(*lhs) {
                                if rule.iter().all(|sym| match sym {
                                    Symbol::NonTerminal(nt) => self.is_nullable(*nt),
                                    _ => false
                                }) {
                                    self.nullable[*lhs as usize] = true;
                                    work_symbols.push(*lhs);
                                }
                            }
                        }
                    }
                }

                pub(super) fn detect_infinite_ambiguity(&self) {
                    let mut colours = [Colour::White; NT_COUNT];
                    let mut iter_lhs = self.iter_lhs().cloned();

                    // Continue doing DFS until there are no more White nodes left
                    while let Some(start_symbol) =
                        iter_lhs.by_ref()
                        .find(|lhs| colours[*lhs as usize] == Colour::White)
                    {
                        let mut stack = vec![start_symbol];

                        while let Some(non_term) = stack.pop() {
                            match colours[non_term as usize] {
                                // Nonterminal was pushed multiple times while it was still White,
                                // so we ignore subsequent occurences
                                Colour::Black => (),
                                // We've explored all descendants, so colour it Black
                                Colour::Gray => colours[non_term as usize] = Colour::Black,

                                Colour::White => {
                                    // Put the node on the current DFS path
                                    colours[non_term as usize] = Colour::Gray;
                                    // Add node back on so we can colour it Black later
                                    stack.push(non_term);

                                    // Get all rhs rules that have no terminal tokens
                                    let derived = self
                                                  .get_iter_rhs(non_term)
                                                  .filter(|rule|
                                                        rule.iter().all(|sym| match sym {
                                                            Symbol::Terminal(_) => false,
                                                            Symbol::NonTerminal(_) => true,
                                                        })
                                                  ).map(|rule|
                                                        rule.iter().map(|sym| sym.non_terminal())
                                                  );

                                    let next_nodes: Vec<NonTerminal> = if self.is_nullable(non_term) {
                                        // For nullable symbols only consider productions with no
                                        // non-nullable symbols. Take all symbols from those rules.
                                        derived
                                        .filter_map(|iter| {
                                            let vec = iter.collect::<Vec<NonTerminal>>();
                                            if vec.iter().all(|nt| self.is_nullable(*nt)) {
                                                Some(vec.into_iter())
                                            } else {
                                                None
                                            }
                                        })
                                        .flatten().collect()
                                    } else {
                                        // For non-nullable symbols only consider productions with
                                        // one non-nullable symbol. Take all non-nullables from
                                        // those rules
                                        derived.map(|iter|
                                            iter.filter(|nt| !self.is_nullable(*nt)).collect::<Vec<NonTerminal>>())
                                        .filter(|vec| vec.len() == 1)
                                        .flat_map(|vec| vec.into_iter()).collect()
                                    };

                                    for nt in next_nodes {
                                        match colours[nt as usize] {
                                            Colour::White => stack.push(nt),
                                            Colour::Black => (),
                                            Colour::Gray =>
                                                panic!("NonTerminal {:?} derives itself, thereby causing infinite ambiguity in the grammar", nt)
                                        }
                                    }
                                }
                            };

                        }
                    }
                }

                pub fn get_iter_rhs(
                    &self,
                    lhs: NonTerminal
                ) -> impl Iterator<Item=&Rule>
                {
                    self.rules.get_iter_rhs(lhs)
                }

                pub fn iter_lhs(&self) -> impl Iterator<Item=&NonTerminal> {
                    static NONTERMINALS: [NonTerminal; NT_COUNT] = [$(NonTerminal::$lhs),*];
                    NONTERMINALS.iter()
                }

                pub fn is_nullable(&self, non_term: NonTerminal) -> bool {
                    self.nullable[non_term as usize]
                }
            }

            // Enum for the infinite ambiguity detection algorithm (graph colouring)
            #[derive(PartialEq, Eq, Clone, Copy)]
            enum Colour {
                Gray,   // Node is currently on the DFS path
                Black,  // Node and all its descendants have been explored
                White,  // Node is unexplored
            }
        }

        use __inner::MakeSymbol;

        pub fn get_grammar() -> __inner::Grammar {
            use $Token::*;
            use __inner::NonTerminal::*;

            let mut __grammar = __inner::Grammar::new();
            grammar!(@rules __grammar, $( $lhs = $rhs )*);
            __grammar.compute_nullable();
            __grammar.detect_infinite_ambiguity();
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

    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
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
             F = [A B C | E]
             G = [D | | E E]
             H = [ | D ]
             I = [ E | ]);

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
        assert!(grammar.is_nullable(NonTerminal::G));
        assert!(grammar.is_nullable(NonTerminal::H));
        assert!(grammar.is_nullable(NonTerminal::I));
    }
}

#[cfg(test)]
mod panic_tests {
    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub enum Tok {
        PLUS,
        MINUS,
    }

    grammar!(null_cycle_grammar <crate::grammar::panic_tests::Tok>:
             S = [S S | S S S | ]);

    #[test]
    #[should_panic(expected = "infinite ambiguity")]
    fn nullable_cycle() {
        null_cycle_grammar::get_grammar();
    }

    grammar!(null_cycle_grammar2 <crate::grammar::panic_tests::Tok>:
             S = [ A B ]
             A = [ B ]
             B = [ S | ]);

    #[test]
    #[should_panic(expected = "infinite ambiguity")]
    fn long_nullable_cycle() {
        null_cycle_grammar2::get_grammar();
    }

    grammar!(cycle_grammar <crate::grammar::panic_tests::Tok>:
             Good = [ PLUS | MINUS ]
             Bad = [ Worse ]
             Worse = [ Worst ]
             Worst = [ Good | Bad ]);

    #[test]
    #[should_panic(expected = "infinite ambiguity")]
    fn non_nullable_cycle() {
        cycle_grammar::get_grammar();
    }
}
