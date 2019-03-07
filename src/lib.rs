#[macro_use]
mod grammar;
use grammar::*;

macro_rules! parser {
    ( $name:ident <$grammar_mod:path> ) => {
        mod $name {
            use $grammar_mod::*;

            use std::collections::HashMap;
            use std::hash::Hash;

            #[derive(Debug)]
            struct Item<'a> {
                lhs: NonTerminal,
                rule: &'a Rule,
                dot: usize,
                from: usize,
            }

            impl<'a> Item<'a> {
                fn new(lhs: NonTerminal, rule: &'a Rule, from: usize) -> Self {
                    Item {
                        lhs,
                        rule,
                        from,
                        dot: 0,
                    }
                }

                fn dot_symbol(&self) -> Option<&'a Symbol> {
                    self.rule.symbol(self.dot)
                }

                fn done(&self) -> bool {
                    self.dot == self.rule.len()
                }

                fn advance(&self) -> Self {
                    assert!(self.dot < self.rule.len());
                    Item {
                        dot: self.dot + 1,
                        ..*self
                    }
                }

                fn clone(&self) -> Self {
                    Item { ..*self }
                }
            }

            #[derive(Debug)]
            struct StateSet<'a>(Vec<Item<'a>>);

            impl<'a> StateSet<'a> {
                fn new() -> Self {
                    StateSet(Vec::new())
                }

                fn push(&mut self, item: Item<'a>) {
                    self.0.push(item);
                }

                fn iter(&self) -> impl Iterator<Item = &Item<'a>> {
                    self.0.iter()
                }

                fn get(&self, i: usize) -> &Item<'a> {
                    &self.0[i]
                }

                fn len(&self) -> usize {
                    self.0.len()
                }
            }

            #[derive(Debug)]
            struct Chart<'a>(Vec<StateSet<'a>>);

            impl<'a> Chart<'a> {
                fn new() -> Self {
                    Chart(Vec::new())
                }

                fn len(&self) -> usize {
                    self.0.len()
                }

                fn push(&mut self, set: StateSet<'a>) {
                    self.0.push(set);
                }

                fn get(&self, i: usize) -> &StateSet<'a> {
                    &self.0[i]
                }

                fn get_mut(&mut self, i: usize) -> &mut StateSet<'a> {
                    &mut self.0[i]
                }
            }

            #[derive(PartialEq, Debug)]
            // Encountered token that does not match any available subparses
            pub struct UnexpectedToken(pub Token);

            #[derive(Debug)]
            // Parse ended when there's still tokens left to be matched
            pub struct UnexpectedEnd;

            #[derive(Debug)]
            pub struct Parser<'a> {
                grammar: &'a Grammar,
                chart: Chart<'a>,
                progress: usize,
                start_symbol: NonTerminal,
            }

            impl<'a> Parser<'a> {
                pub fn new(grammar: &'a Grammar, start_symbol: NonTerminal) -> Self {
                    let mut parser = Self {
                        chart: Chart::new(),
                        grammar,
                        progress: 0,
                        start_symbol,
                    };

                    parser.chart.push(StateSet::new());
                    parser
                }

                fn predict(&mut self, non_term: NonTerminal, has_predicted: &mut [bool]) {
                    if !has_predicted[non_term as usize] {
                        has_predicted[non_term as usize] = true;
                        let progress = self.progress;
                        for rule in self.grammar.get_iter_rhs(non_term) {
                            self.chart
                                .get_mut(progress)
                                .push(Item::new(non_term, rule, progress));
                        }
                    }
                }

                fn scan(&self, item: &Item<'a>, next_set: &mut StateSet<'a>) {
                    next_set.push(item.advance());
                }

                fn complete(&mut self, item: &Item<'a>) {
                    // TODO handle ambiguity
                    assert!(item.done());
                    let from = item.from;
                    // In this case LHS has to be nullable, which means it has already
                    // been advanced for this state set.
                    if from == self.progress { return; }

                    for i in 0..self.chart.get(from).len() {
                        if let Some(sym) = self.chart.get(from).get(i).dot_symbol() {
                            if let Symbol::NonTerminal(nt) = sym {
                                if nt == &item.lhs {
                                    let new_item = self.chart.get(from).get(i).advance();
                                    self.chart.get_mut(self.progress).push(new_item);
                                }
                            }
                        }
                    }
                }

                fn parse_set(&mut self, token: Option<Token>) -> bool {
                    let mut next_set = StateSet::new();
                    let mut has_predicted = [false; NT_COUNT];

                    if self.progress == 0 {
                        self.predict(self.start_symbol, &mut has_predicted);
                    }

                    let mut i = 0;
                    while i < self.chart.get(self.progress).len() {
                        let item = self.chart.get(self.progress).get(i).clone();

                        if let Some(symbol) = item.dot_symbol() {
                            match symbol {
                                Symbol::NonTerminal(nt) => {
                                    self.predict(*nt, &mut has_predicted);
                                }
                                Symbol::Terminal(t) => {
                                    token.map(|tok| {
                                        if *t == tok {
                                            self.scan(&item, &mut next_set);
                                        }
                                    });
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

                pub fn parse_token(mut self, token: Token) -> Result<Self, UnexpectedToken> {
                    if self.parse_set(Some(token)) {
                        Ok(self)
                    } else {
                        Err(UnexpectedToken(token))
                    }
                }

                pub fn finish_parse(mut self) -> Result<(), UnexpectedEnd> {
                    let continued = self.parse_set(None);
                    assert!(!continued);

                    if self
                        .chart
                        .get(self.progress)
                        .iter()
                        .any(|item| item.done() && item.from == 0 && item.lhs == self.start_symbol)
                    {
                        Ok(())
                    } else {
                        Err(UnexpectedEnd)
                    }
                }
            }
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    pub enum Token {
        NUM,
        PLUS,
        MINUS,
        LB,
        RB,
    }

    grammar!(TestGrammar <crate::tests::Token>:
             expr = [NUM |
                     expr PLUS expr |
                     expr MINUS expr |
                     LB expr RB]
    );

    parser!(TestParser<crate::tests::TestGrammar>);

    #[test]
    fn basic() {
        use TestGrammar::*;
        use TestParser::*;

        let grammar = get_grammar();
        let mut parser = Parser::new(&grammar, NonTerminal::expr);

        parser = parser.parse_token(Token::NUM).unwrap();
        parser = parser.parse_token(Token::PLUS).unwrap();
        parser = parser.parse_token(Token::NUM).unwrap();
        parser.finish_parse().unwrap();
    }

    #[test]
    fn nested() {
        use TestGrammar::*;
        use TestParser::*;
        use Token::*;

        let grammar = get_grammar();
        let mut parser = Parser::new(&grammar, NonTerminal::expr);

        for tok in [NUM, PLUS, LB, NUM, MINUS, NUM, RB].iter() {
            parser = parser.parse_token(*tok).unwrap();
        }
        parser.finish_parse().unwrap();
    }

    #[test]
    fn token_error() {
        use TestGrammar::*;
        use TestParser::*;
        use Token::*;

        let grammar = get_grammar();
        let mut parser = Parser::new(&grammar, NonTerminal::expr);

        for tok in [LB, LB, NUM, RB, RB].iter() {
            parser = parser.parse_token(*tok).unwrap();
        }
        assert!(parser.parse_token(RB).unwrap_err() == UnexpectedToken(RB));
    }

    #[test]
    fn end_error() {
        use TestGrammar::*;
        use TestParser::*;
        use Token::*;

        let grammar = get_grammar();
        let mut parser = Parser::new(&grammar, NonTerminal::expr);

        for tok in [LB, LB, NUM].iter() {
            parser = parser.parse_token(*tok).unwrap();
        }
        parser.finish_parse().unwrap_err();
    }
}
