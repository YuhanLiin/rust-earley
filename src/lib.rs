mod grammar;
use grammar::*;

struct Item<'a, S: 'a, R: Rule<'a, Symbol=S>, NT> {
    lhs: &'a NT,
    rule: &'a R,
    dot: usize,
    from: usize,
}

impl<'a, S, R, NT> Item<'a, S, R, NT> 
where R: Rule<'a, Symbol=S>, S: 'a
{
    fn new(lhs: &'a NT, rule: &'a R, from: usize) -> Self {
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
}

struct Parser<'a, G, S: 'a, R, NT: 'a>
where R: Rule<'a, Symbol=S>, G: Grammar<'a, NonTerminal=NT, Rule=R>
{
    grammar: &'a G,
    chart: Vec<Vec<Item<'a, S, R, NT>>>,
    progress: usize,
}

impl<'a, G, S: 'a, R, NT: 'a, T> Parser<'a, G, S, R, NT> 
where R: Rule<'a, Symbol=S>,
      G: Grammar<'a, NonTerminal=NT, Rule=R>,
      S: Symbol<Terminal=T, NonTerminal=NT>,
      NT: Eq
{
    fn new(grammar: &'a G) -> Self {
        Self { chart: Vec::new(), grammar, progress: 0 }
    }

    fn get_set(&self, i: usize) -> &Vec<Item<'a, S, R, NT>> {
        &self.chart[i]    
    }

    fn get_set_or_add(&mut self, i: usize) -> &mut Vec<Item<'a, S, R, NT>> {
        assert!(self.chart.len() - i <= 2);
        if i >= self.chart.len() {
            self.chart.push(Vec::new());
        }
        // Given the above assert, this should not panic
        &mut self.chart[i]
    }

    fn predict(&mut self, non_term: &'a NT) {
        // TODO repeat prevention
        let progress = self.progress;
        for rule in self.grammar.get_iter_rhs(non_term) {
            self.get_set_or_add(progress).
                 push(Item::new(non_term, rule, progress));
        }
    }

    fn scan(&mut self, item: &Item<'a, S, R, NT>) {
        // TODO token checking
        self.get_set_or_add(self.progress + 1).push(item.advance());
    }

    fn complete(&mut self, item: &Item<'a, S, R, NT>) {
        assert!(item.done());
        let mut temp = Vec::new();
        let from = item.from;
        for old_item in self.get_set(from) {
            if let Some(sym) = old_item.dot_symbol() {
                if let Some(nt) = sym.nonterminal() {
                    if nt == item.lhs {
                        temp.push(old_item.advance());
                    }
                }
            }
        }
        for item in temp {
            self.get_set_or_add(self.progress + 1).push(item);
        }
    }

    fn parse_token(&mut self, token: T) {
        for item in self.get_set(self.progress) {
        }
        self.progress += 1;

    }
}
