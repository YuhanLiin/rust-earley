macro_rules! grammar {
    ( @rules $grammar:ident, ) => ();

    ( @rules $grammar:ident, $lhs:ident = [ $($rhs:ident)* ];
      $( $tail:tt )* ) => (
        $grammar.add_rule($lhs, vec![ $(Symbol::new($rhs)),* ]);
        grammar!(@rules $grammar, $($tail)*)
    );

    ( $name:ident, $Token:path,
      $( $lhs:ident = $rhs:tt; )* ) => (

        mod $name {
            use std::collections::HashMap;

            #[derive(PartialEq)]
            #[derive(Eq)]
            #[derive(Hash)]
            enum NonTerminal {
                $($lhs),*
            }

            enum Symbol{
                Terminal($Token),
                NonTerminal(NonTerminal),
            }

            struct Rule(Vec<Symbol>);

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

            pub struct Grammar {
                rules: HashMap<NonTerminal, Rule>,
            }

            impl Grammar {
                fn new() -> Self {
                    Grammar { rules: HashMap::new() }
                }

                fn add_rule(&mut self, lhs: NonTerminal, rhs: Vec<Symbol>) {
                    self.rules.insert(lhs, Rule(rhs));
                }
            }

            use $Token::*;
            use NonTerminal::*;

            fn get_grammar() -> Grammar {
                let mut grammar = Grammar::new();
                grammar!(@rules grammar, $( $lhs = $rhs; )*);
                grammar
            }

        }
    )
}

enum Tok {
    A, B
}

grammar!(Name, crate::Tok, a = [A B];);

#[cfg(test)]
mod tests {
    use super::*;

    struct Tok;
    grammar!(Name, crate::tests::Tok, a = b;);

    #[test]
    fn it_works() {
        let (a, b) = (1, 2);
        grammar_rules!(a = b; b = a;);
        assert_eq!(2 + 2, 4);
    }
}
