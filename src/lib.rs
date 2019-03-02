macro_rules! grammar {
    ( @rules $grammar:ident, ) => ();

    ( @rules $grammar:ident, $lhs:ident = [ $($rhs:tt)* ]
      $( $tail:tt )* ) => (
        $grammar!(@rhs $grammar, $lhs, $($rhs)*);
        grammar!(@rules $grammar, $($tail)*)
    );

    ( @rhs $grammar:ident, $lhs:ident, ) => ();

    ( @rhs $grammar:ident, $lhs:ident, $($symbol:ident)* $( | $($tail:tt)* )? ) => (
        $grammar.add_rule($lhs, vec![ $(Symbol::new($symbol)),* ]);
        grammar!(@rhs $grammar, $lhs, $( $($tail)* )?)
    );

    ( $name:ident, $Token:path,
      $( $lhs:ident = $rhs:tt )* ) => (

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

            type ProdRule = Vec<Symbol>;

            pub struct Grammar {
                rules: HashMap<NonTerminal, Vec<ProdRule>>,
            }

            impl Grammar {
                fn new() -> Self {
                    Grammar { rules: HashMap::new() }
                }

                fn add_rule(&mut self, lhs: NonTerminal, rhs: Vec<Symbol>) {
                    let prod_rules = self.rules.entry(lhs).or_insert(Vec::new());
                    prod_rules.push(rhs);
                }
            }

            use $Token::*;
            use NonTerminal::*;

            fn get_grammar() -> Grammar {
                let mut grammar = Grammar::new();
                grammar!(@rules grammar, $( $lhs = $rhs )*);
                grammar
            }

        }
    )
}


enum Tok {
    NUM, PLUS, MINUS,
}

grammar!(Name, crate::Tok,
         stmt = [expr | ]
         expr = [NUM | expr PLUS expr | expr MINUS expr]
);

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
