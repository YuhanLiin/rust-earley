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


struct StateSet<'a, S: 'a, R: Rule<'a, Symbol=S>, NT> (Vec<Item<'a, S, R, NT>>);

impl<'a, S, R, NT> StateSet<'a, S, R, NT> 
where R: Rule<'a, Symbol=S>, S: 'a
{
    fn new() -> Self { Self (Vec::new()) }

    fn push(&mut self, item: Item<'a, S, R, NT>) {
        self.0.push(item);
    }

    fn merge(&mut self, mut other: Self) {
        self.0.append(&mut other.0);
    }

    fn iter(&self) -> impl Iterator<Item=&Item<'a, S, R, NT>> {
        self.0.iter()
    }
}

struct Chart<'a, S: 'a, R: Rule<'a, Symbol=S>, NT> (Vec<StateSet<'a, S, R, NT>>);

impl<'a, S, R, NT> Chart<'a, S, R, NT> 
where R: Rule<'a, Symbol=S>, S: 'a
{
    fn new() -> Self { Self(Vec::new()) }

    fn len(&self) -> usize { self.0.len() }

    fn push(&mut self, set: StateSet<'a, S, R, NT>) { 
        self.0.push(set);
    }

    fn get(&self, i: usize) -> &StateSet<'a, S, R, NT> {
        &self.0[i]
    }

    fn get_mut(&mut self, i: usize) -> &mut StateSet<'a, S, R, NT> {
        &mut self.0[i]
    }
}

struct Parser<'a, G, S: 'a, R, NT: 'a>
where R: Rule<'a, Symbol=S>, G: Grammar<'a, NonTerminal=NT, Rule=R>
{
    grammar: &'a G,
    chart: Chart<'a, S, R, NT>,
    progress: usize,
}

impl<'a, G, S: 'a, R, NT: 'a, T> Parser<'a, G, S, R, NT> 
where R: Rule<'a, Symbol=S>,
      G: Grammar<'a, NonTerminal=NT, Rule=R>,
      S: Symbol<Terminal=T, NonTerminal=NT>,
      NT: Eq
{
    fn new(grammar: &'a G) -> Self {
        Self { chart: Chart::new(), grammar, progress: 0 }
    }

    fn predict(&mut self, non_term: &'a NT) {
        // TODO repeat prevention
        let progress = self.progress;
        for rule in self.grammar.get_iter_rhs(non_term) {
            self.chart.get_mut(progress).
                 push(Item::new(non_term, rule, progress));
        }
    }

    fn scan(&mut self, item: &Item<'a, S, R, NT>) {
        // TODO token checking
        self.chart.get_mut(self.progress + 1).push(item.advance());
    }

    fn complete(&mut self, item: &Item<'a, S, R, NT>) {
        assert!(item.done());
        let mut temp = Vec::new();
        let from = item.from;
        for old_item in self.chart.get(from).iter() {
            if let Some(sym) = old_item.dot_symbol() {
                if let Some(nt) = sym.nonterminal() {
                    if nt == item.lhs {
                        temp.push(old_item.advance());
                    }
                }
            }
        }
        for item in temp {
            self.chart.get_mut(self.progress + 1).push(item);
        }
    }

    fn parse_token(&mut self, token: T) {
        for item in self.chart.get(self.progress).iter() {
            if let Some(symbol) = item.dot_symbol() {
                
            } else {
                //self.complete(item);
            }
        }
        self.progress += 1;
    }
}
