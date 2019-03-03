mod grammar;
use grammar::*;

struct Item<'a, S: 'a, R: Rule<'a, Symbol=S>, NT> {
    lhs: &'a NT,
    rule: &'a R,
    dot: usize,
}

impl<'a, S, R, NT> Item<'a, S, R, NT> 
where R: Rule<'a, Symbol=S>, S: 'a
{
    fn new(lhs: &'a NT, rule: &'a R) -> Self {
        Item { lhs, rule, dot: 0 }
    }

    fn dot_symbol(&self) -> &'a S {
        self.rule.symbol(self.dot)
    }

    fn advance(&mut self) {
        self.dot += 1;
        assert!(self.dot <= self.rule.len());
    }
}

struct Parser<'a, G, S: 'a, R, NT: 'a>
where R: Rule<'a, Symbol=S>, G: Grammar<'a, NonTerminal=NT, Rule=R>
{
    grammar: &'a G,
    chart: Vec<Vec<Item<'a, S, R, NT>>>,
    progress: usize,
}

impl<'a, G, S: 'a, R, NT: 'a> Parser<'a, G, S, R, NT> 
where R: Rule<'a, Symbol=S>, G: Grammar<'a, NonTerminal=NT, Rule=R>
{
    fn new(grammar: &'a G) -> Self {
        Self { chart: Vec::new(), grammar, progress: 0 }
    }

    fn start_parse(&mut self, starting_symbol: &'a NT) {
        assert_eq!(self.chart.len(), 0);
        self.chart.push(Vec::new());
        for rule in self.grammar.get_iter_rhs(starting_symbol) {
            self.chart[0].push(Item::new(starting_symbol, rule));
        }
    }

}
