#[macro_use]
mod grammar;
use grammar::*;

use std::collections::HashMap;
use std::hash::Hash;

macro_rules! gen {
    ($type:ident) => ( $type<'a, S, R, NT> );
}

struct Item<'a, S: 'a, R: Rule<'a, Symbol=S>, NT: Copy> {
    lhs: NT,
    rule: &'a R,
    dot: usize,
    from: usize,
}

impl<'a, S, R, NT: Copy> gen!(Item)
where R: Rule<'a, Symbol=S>, S: 'a
{
    fn new(lhs: NT, rule: &'a R, from: usize) -> Self {
        Item { lhs, rule, from, dot: 0 }
    }

    fn dot_symbol(&self) -> Option<&'a S> {
        self.rule.symbol(self.dot)
    }

    fn done(&self) -> bool {
        self.dot == self.rule.len()
    }

    fn advance(&self) -> Self {
        assert!(self.dot < self.rule.len());
        Item { dot: self.dot + 1, ..*self }
    }

    fn clone(&self) -> Self {
        Item { ..*self }
    }
}


struct StateSet<'a, S: 'a, R: Rule<'a, Symbol=S>, NT: Copy> (Vec<gen!(Item)>);

impl<'a, S, R, NT: Copy> gen!(StateSet)
where R: Rule<'a, Symbol=S>, S: 'a
{
    fn new() -> Self { Self (Vec::new()) }

    fn push(&mut self, item: gen!(Item)) {
        self.0.push(item);
    }

    fn iter(&self) -> impl Iterator<Item=&gen!(Item)> {
        self.0.iter()
    }

    fn get(&self, i: usize) -> &gen!(Item) {
        &self.0[i]
    }

    fn len(&self) -> usize { self.0.len() }
}

struct Chart<'a, S: 'a, R: Rule<'a, Symbol=S>, NT: Copy> (Vec<gen!(StateSet)>);

impl<'a, S, R, NT: Copy> gen!(Chart)
where R: Rule<'a, Symbol=S>, S: 'a
{
    fn new() -> Self { Self(Vec::new()) }

    fn len(&self) -> usize { self.0.len() }

    fn push(&mut self, set: gen!(StateSet)) {
        self.0.push(set);
    }

    fn get(&self, i: usize) -> &gen!(StateSet) {
        &self.0[i]
    }

    fn get_mut(&mut self, i: usize) -> &mut gen!(StateSet) {
        &mut self.0[i]
    }
}

#[derive(PartialEq)]
pub enum ParserError<T> {
    // Encountered token that does not match any available subparses
    UnexpectedToken(T),
    // Parse ended when there's still tokens left to be matched
    UnexpectedEnd,
    // Returned when parser is called after parsing has completed or erred
    ParseEnded,
}

struct Parser<'a, G, S: 'a, R, NT: 'a + Copy>
where R: Rule<'a, Symbol=S>, G: Grammar<'a, NonTerminal=NT, Rule=R>
{
    grammar: &'a G,
    chart: gen!(Chart),
    progress: usize,
    start_symbol: NT,
    finished: bool
}

impl<'a, G, S: 'a, R, NT: 'a, T> Parser<'a, G, S, R, NT>
where R: Rule<'a, Symbol=S>,
      G: Grammar<'a, NonTerminal=NT, Rule=R>,
      S: Symbol<Terminal=T, NonTerminal=NT>,
      NT: Eq + Copy + Hash + NonTerminal,
      T: Eq + Copy,
{
    pub fn new(grammar: &'a G, start_symbol: NT) -> Self {
        let mut parser = Self {
            chart: Chart::new(),
            grammar,
            progress: 0,
            start_symbol,
            finished: false
        };

        parser.chart.push(StateSet::new());
        parser
    }

    fn predict(&mut self, non_term: NT, has_predicted: &mut HashMap<NT, bool>) {
        if !*has_predicted.entry(non_term).or_insert(false) {
            has_predicted.insert(non_term, true);
            let progress = self.progress;
            for rule in self.grammar.get_iter_rhs(&non_term) {
                self.chart.get_mut(progress).
                     push(Item::new(non_term, rule, progress));
            }
        }
    }

    fn scan(&self, item: &gen!(Item), next_set: &mut gen!(StateSet)) {
        next_set.push(item.advance());
    }

    fn complete(&mut self, item: &gen!(Item)) {
        assert!(item.done());
        let from = item.from;
        for i in 0..self.chart.get(from).len() {
            if let Some(sym) = self.chart.get(from).get(i).dot_symbol() {
                if let Some(nt) = sym.nonterminal() {
                    if nt == &item.lhs {
                        let new_item = self.chart.get(from).get(i).advance();
                        self.chart.get_mut(self.progress).push(new_item);
                    }
                }
            }
        }
    }

    fn parse_set(&mut self, token: Option<&T>) -> bool {
        let mut next_set = StateSet::new();
        let mut has_predicted = HashMap::new();

        if self.progress == 0 {
            self.predict(self.start_symbol, &mut has_predicted);
        }

        let mut i = 0;
        while i < self.chart.get(self.progress).len() {
            let item: gen!(Item) = self.chart.get(self.progress).get(i).clone();

            if let Some(symbol) = item.dot_symbol() {
                if let Some(nt) = symbol.nonterminal() {
                    self.predict(*nt, &mut has_predicted);
                } else if let Some(tok) = token {
                    let t = symbol.terminal().unwrap();
                    if t == tok {
                        self.scan(&item, &mut next_set);
                    }
                }
            } else {
                self.complete(&item);
            }
            i += 1;
        }

        if next_set.len() == 0 {
            false
        } else {
            self.chart.push(next_set);
            self.progress += 1;
            true
        }
    }

    pub fn parse_token(&mut self, token: &T) -> Result<(), ParserError<T>> {
        if self.finished { return Err(ParserError::ParseEnded); }

        if self.parse_set(Some(token)) {
            Ok(())
        } else {
            self.finished = true;
            Err(ParserError::UnexpectedToken(*token))
        }
    }

    pub fn finish_parse(&mut self) -> Result<(), ParserError<T>> {
        if self.finished { return Err(ParserError::ParseEnded); }

        self.finished = true;
        let continued = self.parse_set(None);
        assert!(!continued);

        if self.chart.get(self.progress).iter().any(|item| {
            item.done() && item.from == 0 && item.lhs == self.start_symbol
        }) {
            Ok(())
        } else {
            Err(ParserError::UnexpectedEnd)
        }
    }
}

#[cfg(test)]
mod tests{
    use super::*;

    #[derive(Debug)]
    #[derive(PartialEq, Eq, Clone, Copy)]
    pub enum Tok {
        NUM, PLUS, MINUS, LB, RB
    }

    grammar!(TestGrammar <crate::tests::Tok>:
             expr = [NUM | 
                     expr PLUS expr | 
                     expr MINUS expr |
                     LB expr RB]
    );

    #[test]
    fn basic() {
        use TestGrammar::*;

        let grammar = get_grammar();
        let mut parser = Parser::new(&grammar, NonTerminal::expr);

        assert!(parser.parse_token(&Tok::NUM).is_ok());
        assert!(parser.parse_token(&Tok::PLUS).is_ok());
        assert!(parser.parse_token(&Tok::NUM).is_ok());
        assert!(parser.finish_parse().is_ok());
        assert!(parser.finish_parse().unwrap_err() == ParserError::ParseEnded);
        assert!(
            parser.parse_token(&Tok::NUM).unwrap_err() == ParserError::ParseEnded);
    }

    #[test]
    fn nested() {
        use TestGrammar::*;
        use Tok::*;

        let grammar = get_grammar();
        let mut parser = Parser::new(&grammar, NonTerminal::expr);

        for tok in [NUM, PLUS, LB, NUM, MINUS, NUM, RB].iter() {
            assert!(parser.parse_token(tok).is_ok());
        }
        assert!(parser.finish_parse().is_ok());
    }

    #[test]
    fn token_error() {
        use TestGrammar::*;
        use Tok::*;

        let grammar = get_grammar();
        let mut parser = Parser::new(&grammar, NonTerminal::expr);

        for tok in [LB, LB, NUM, RB, RB].iter() {
            assert!(parser.parse_token(tok).is_ok());
        }
        assert!(parser.parse_token(&RB).unwrap_err() == 
                ParserError::UnexpectedToken(RB));
        assert!(parser.finish_parse().unwrap_err() == ParserError::ParseEnded);
    }

    #[test]
    fn end_error() {
        use TestGrammar::*;
        use Tok::*;

        let grammar = get_grammar();
        let mut parser = Parser::new(&grammar, NonTerminal::expr);

        for tok in [LB, LB, NUM].iter() {
            assert!(parser.parse_token(tok).is_ok());
        }
        assert!(parser.finish_parse().unwrap_err() == ParserError::UnexpectedEnd);
        assert!(parser.parse_token(&RB).unwrap_err() == ParserError::ParseEnded);
    }
}
