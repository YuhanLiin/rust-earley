#[macro_use]
extern crate grammar;

use earley::parser;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Token {
    NUM,
    PLUS,
    MINUS,
    LB,
    RB,
}

grammar!(test_grammar <crate::Token>:
         Expr = [NUM |
                 Expr PLUS Expr |
                 Expr MINUS Expr |
                 LB Expr RB]
);

parser!(test_parser<crate::test_grammar>);

macro_rules! parse_tokens {
    ( $parser:ident, $tokens:expr ) => {
        for token in $tokens.iter() {
            $parser = $parser.parse_token(*token).unwrap();
        }
    };
}

#[test]
fn basic() {
    use test_grammar::*;
    use test_parser::*;
    use Token::*;

    let grammar = get_grammar();
    let mut parser = Parser::new(&grammar, NonTerminal::Expr);

    parse_tokens!(parser, [NUM, PLUS, NUM]);
    parser.finish_parse().unwrap();
}

#[test]
fn nested() {
    use test_grammar::*;
    use test_parser::*;
    use Token::*;

    let grammar = get_grammar();
    let mut parser = Parser::new(&grammar, NonTerminal::Expr);

    parse_tokens!(parser, [NUM, PLUS, LB, NUM, MINUS, NUM, RB]);
    parser.finish_parse().unwrap();
}

#[test]
fn token_error() {
    use test_grammar::*;
    use test_parser::*;
    use Token::*;

    let grammar = get_grammar();
    let mut parser = Parser::new(&grammar, NonTerminal::Expr);

    parse_tokens!(parser, [LB, LB, NUM, RB, RB]);
    parser.parse_token(RB).unwrap_err();
}

#[test]
fn end_error() {
    use test_grammar::*;
    use test_parser::*;
    use Token::*;

    let grammar = get_grammar();
    let mut parser = Parser::new(&grammar, NonTerminal::Expr);

    parse_tokens!(parser, [LB, LB, NUM]);
    parser.finish_parse().unwrap_err();
}

grammar!(nullable_grammar <crate::Token>:
         A = [ | NUM ]
         B = [ D B | A ]
         C = [ B | C NUM ]
         D = [ PLUS ]);

parser!(nullable_parser<crate::nullable_grammar>);

#[test]
fn nullable_parse() {
    use nullable_grammar::*;
    use nullable_parser::*;
    use Token::*;

    let grammar = get_grammar();
    let original_parser = Parser::new(&grammar, NonTerminal::C);
    println!("{:?}", grammar.is_nullable(NonTerminal::C));
    println!("{:?}", grammar.is_nullable(NonTerminal::B));
    println!("{:?}", grammar.is_nullable(NonTerminal::A));

    let parser = original_parser.clone();
    parser.finish_parse().unwrap();

    let mut parser = original_parser.clone();
    parse_tokens!(parser, [NUM, NUM, NUM, NUM]);
    parser.finish_parse().unwrap();

    let parser = original_parser.clone();
    parser.parse_token(PLUS).unwrap();

    let parser = original_parser.clone();
    parser.parse_token(MINUS).unwrap_err();
}

grammar!(rec_grammar <crate::Token>:
         Start = [ Right | Mid ]
         Right = [ NUM Right | ]
         Mid = [ LB Mid RB | LB Mid | PLUS ]);

parser!(rec_parser<crate::rec_grammar>);

#[test]
fn rec_leo_parse() {
    use rec_grammar::*;
    use rec_parser::*;
    use Token::*;

    let grammar = get_grammar();
    let original_parser = Parser::new(&grammar, NonTerminal::Start);

    let mut parser = original_parser.clone();
    parse_tokens!(parser, [NUM, NUM, NUM, NUM, NUM, NUM, NUM]);
    parser.finish_parse().unwrap();

    let mut parser = original_parser.clone();
    parse_tokens!(parser, [LB, LB, LB, PLUS, RB]);
    parser.finish_parse().unwrap();
}
