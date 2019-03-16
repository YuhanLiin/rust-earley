#[macro_use]
mod grammar;

macro_rules! parser {
    ( $name:ident <$grammar_mod:path> ) => {
        #[allow(unused)]
        mod $name {
            use $grammar_mod::*;

            #[derive(Debug, Clone)]
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

                fn is_at_last(&self) -> bool {
                    self.dot == self.rule.len() - 1
                }
            }

            #[derive(Debug, Clone)]
            struct Chart<'a> {
                // Earley Items
                items: Vec<Item<'a>>,
                // Starting indices of each state set in the items vector
                boundaries: Vec<usize>,
            }

            impl<'a> Chart<'a> {
                fn new() -> Self {
                    Chart {
                        items: vec![],
                        boundaries: vec![],
                    }
                }

                fn len(&self) -> usize {
                    self.boundaries.len()
                }

                fn push_set(&mut self) {
                    self.boundaries.push(self.items.len());
                }

                fn push_item(&mut self, item: Item<'a>) {
                    self.items.push(item);
                }

                fn get(&self, i: usize) -> &[Item<'a>] {
                    let len = self.items.len();
                    let start = self.boundaries[i];
                    let end = self.boundaries.get(i + 1).unwrap_or_else(|| &len);
                    &self.items[start..*end]
                }
            }

            // Mapping between postdot symbols and items for each state set
            // Used during completion
            #[derive(Clone, Debug)]
            struct PostDot(Vec<[Vec<usize>; NT_COUNT]>);

            impl PostDot {
                fn new() -> Self {
                    PostDot(vec![])
                }

                fn push_set(&mut self) {
                    self.0.push(Default::default());
                }

                fn push_idx(&mut self, non_term: NonTerminal, idx: usize) {
                    self.0.last_mut().unwrap()[non_term as usize].push(idx);
                }

                fn iter_idx(
                    &self,
                    i: usize,
                    non_term: NonTerminal,
                ) -> impl Iterator<Item = &usize> {
                    self.0[i][non_term as usize].iter()
                }
            }

            #[derive(Clone, Debug)]
            struct LeoItems<'a>(Vec<[Option<Item<'a>>; NT_COUNT]>);

            impl<'a> LeoItems<'a> {
                fn new() -> Self {
                    LeoItems(vec![])
                }

                fn push_set(&mut self) {
                    self.0.push(Default::default());
                }

                fn set_leo(&mut self, non_term: NonTerminal, item: Item<'a>) {
                    assert!(item.is_at_last());
                    let arr = self.0.last_mut().unwrap();
                    arr[non_term as usize] = Some(item);
                }

                fn get_leo(&self, from: usize, non_term: NonTerminal) -> Option<&Item<'a>> {
                    self.0[from][non_term as usize].as_ref()
                }
            }

            #[derive(PartialEq, Debug)]
            // Unexpected token or end of parse encountered
            pub struct SyntaxError;

            #[derive(Debug, Clone)]
            pub struct Parser<'a> {
                grammar: &'a Grammar,
                tokens: Vec<Token>,
                chart: Chart<'a>,
                postdot: PostDot,
                leo: LeoItems<'a>,
                progress: usize,
                start_symbol: NonTerminal,
            }

            impl<'a> Parser<'a> {
                pub fn new(grammar: &'a Grammar, start_symbol: NonTerminal) -> Self {
                    let mut parser = Self {
                        chart: Chart::new(),
                        tokens: vec![],
                        postdot: PostDot::new(),
                        leo: LeoItems::new(),
                        grammar,
                        progress: 0,
                        start_symbol,
                    };

                    parser.push_set();
                    parser
                }

                fn push_set(&mut self) {
                    self.chart.push_set();
                    self.postdot.push_set();
                    self.leo.push_set();
                }

                fn predict(&mut self, non_term: NonTerminal, has_predicted: &mut [bool]) {
                    if !has_predicted[non_term as usize] {
                        has_predicted[non_term as usize] = true;
                        let progress = self.progress;
                        for rule in self.grammar.get_iter_rhs(non_term) {
                            self.chart.push_item(Item::new(non_term, rule, progress));
                        }
                    }
                }

                fn advance_empty(&mut self, non_term: NonTerminal, item: &Item<'a>) {
                    if self.grammar.is_nullable(non_term) {
                        self.chart.push_item(Item::advance(item));
                    }
                }

                fn complete(&mut self, item: &Item<'a>) {
                    // TODO handle ambiguity
                    assert!(item.done());
                    let from = item.from;
                    // In this case LHS has to be nullable, which means it has already
                    // been advanced for this state set.
                    if from == self.progress {
                        return;
                    }

                    // If a Leo Item is available, complete it and add it to the set
                    let found_leo = if let Some(complete_item) = self.leo.get_leo(from, item.lhs) {
                        assert!(complete_item.is_at_last());
                        self.chart.push_item(complete_item.advance());
                        true
                    } else {
                        false
                    };

                    for idx in self.postdot.iter_idx(from, item.lhs) {
                        let old_item = &self.chart.get(from)[*idx];
                        if !found_leo || !old_item.is_at_last() {
                            self.chart.push_item(old_item.advance());
                        }
                    }
                }

                fn parse_set(&mut self, token: Option<Token>) -> bool {
                    let mut has_predicted = [false; NT_COUNT];
                    let mut scan_idx = Vec::new();

                    if self.progress == 0 {
                        self.predict(self.start_symbol, &mut has_predicted);
                    }

                    let mut i = 0;
                    while i < self.chart.get(self.progress).len() {
                        let item = self.chart.get(self.progress)[i].clone();

                        if let Some(symbol) = item.dot_symbol() {
                            match symbol {
                                Symbol::NonTerminal(nt) => {
                                    self.postdot.push_idx(*nt, i);
                                    self.advance_empty(*nt, &item);
                                    self.predict(*nt, &mut has_predicted);
                                }
                                Symbol::Terminal(t) => {
                                    token.map(|tok| {
                                        if *t == tok {
                                            scan_idx.push(i);
                                        }
                                    });
                                }
                            }
                        } else {
                            self.complete(&item);
                        }
                        i += 1;
                    }

                    self.leo_item_pass();

                    if scan_idx.len() == 0 {
                        false
                    } else {
                        self.tokens.push(token.unwrap());
                        self.scan_pass(&scan_idx);
                        self.progress += 1;
                        true
                    }
                }

                fn leo_item_pass(&mut self) {
                    for lhs in self.grammar.iter_lhs() {
                        let (postdot, progress, chart) =
                            (&self.postdot, &self.progress, &self.chart);
                        let iter = || {
                            postdot
                                .iter_idx(*progress, *lhs)
                                .map(|i| &chart.get(*progress)[*i])
                                .filter(|item| item.is_at_last())
                        };

                        // If there's only one item of the form A -> xyz . B, create Leo item for B
                        if iter().count() == 1 {
                            let item = iter().next().unwrap();

                            let item = if let Some(leo_item) = self.leo.get_leo(item.from, item.lhs)
                            {
                                leo_item.clone()
                            } else {
                                item.clone()
                            };

                            self.leo.set_leo(*lhs, item);
                        }
                    }
                }

                fn scan_pass(&mut self, scan_idx: &Vec<usize>) {
                    self.push_set();
                    for i in scan_idx {
                        let item = &self.chart.get(self.progress)[*i];
                        self.chart.push_item(item.advance());
                    }
                }

                pub fn parse_token(mut self, token: Token) -> Result<Self, SyntaxError> {
                    if self.parse_set(Some(token)) {
                        Ok(self)
                    } else {
                        Err(SyntaxError)
                    }
                }

                pub fn finish_parse(mut self) -> Result<EarleyResult<'a>, SyntaxError> {
                    let continued = self.parse_set(None);
                    assert!(!continued);

                    if self
                        .chart
                        .get(self.progress)
                        .iter()
                        .any(|item| item.done() && item.from == 0 && item.lhs == self.start_symbol)
                    {
                        Ok(EarleyResult(self))
                    } else {
                        Err(SyntaxError)
                    }
                }
            }

            #[derive(Debug, Clone)]
            pub struct EarleyResult<'a>(Parser<'a>);

            impl<'a> EarleyResult<'a> {
                fn search_subitems(
                    &self,
                    item: &Item<'a>,
                    chart_idx: usize,
                    rule_idx: usize,
                ) -> Option<Vec<&Item<'a>>> {
                    let symbol = item.rule.symbol(rule_idx).unwrap();

                    match symbol {
                        Symbol::NonTerminal(nt) => {
                            // Loop thru each completed item in current state set that completes
                            // our target nonterminal symbol. Returns on the first match.
                            for completed in self
                                .0
                                .chart
                                .get(chart_idx)
                                .iter()
                                .filter(|item| item.lhs == *nt && item.done())
                            {
                                if rule_idx == 0 {
                                    // If we're at the first symbol of the rule, check if the
                                    // completed nonterminal is from the same state set as the rule
                                    if completed.from == item.from {
                                        let mut list = Vec::with_capacity(item.rule.len());
                                        list.push(completed);
                                        return Some(list);
                                    }
                                } else {
                                    // Recursively search for the next symbol in the rule. If a
                                    // sequence is found, add the completed item to it and return it.
                                    let mut result =
                                        self.search_subitems(item, completed.from, rule_idx - 1);
                                    if let Some(mut list) = result {
                                        list.push(completed);
                                        return Some(list);
                                    }
                                };
                            }
                        }
                        Symbol::Terminal(t) => {
                            // chart_idx > 0, since a scan can never end at state set 0
                            let token = self.0.tokens[chart_idx - 1];

                            if token == *t {
                                if rule_idx == 0 {
                                    return Some(Vec::with_capacity(item.rule.len()));
                                } else {
                                    return self.search_subitems(item, chart_idx - 1, rule_idx - 1);
                                }
                            }
                        }
                    }

                    return None;
                }

                fn semantic_actions(&self, finished_item: &Item<'a>, end_idx: usize) {
                    let sub_items = self
                        .search_subitems(finished_item, end_idx, finished_item.rule.len())
                        .unwrap();
                    let mut sub_items = sub_items.iter().peekable();

                    for sym in finished_item.rule.iter() {
                        match sym {
                            Symbol::NonTerminal(nt) => {
                                let item = sub_items.next().unwrap();
                                let end =
                                    sub_items.peek().map(|i| i.from).unwrap_or_else(|| end_idx);
                                self.semantic_actions(item, end);
                            }
                            Symbol::Terminal(t) => {
                                // TODO do something to token
                            }
                        }
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

    grammar!(test_grammar <crate::tests::Token>:
             Expr = [NUM |
                     Expr PLUS Expr |
                     Expr MINUS Expr |
                     LB Expr RB]
    );

    parser!(test_parser<crate::tests::test_grammar>);

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

    grammar!(nullable_grammar <crate::tests::Token>:
             A = [ | NUM ]
             B = [ D B | A ]
             C = [ B | C NUM ]
             D = [ PLUS ]);

    parser!(nullable_parser<crate::tests::nullable_grammar>);

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

    grammar!(rec_grammar <crate::tests::Token>:
             Start = [ Right | Mid ]
             Right = [ NUM Right | ]
             Mid = [ LB Mid RB | LB Mid | PLUS ]);

    parser!(rec_parser<crate::tests::rec_grammar>);

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
}
