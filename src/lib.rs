mod grammar;
use grammar::*;

macro_rules! gen {
    ($type:ident) => ( $type<'a, S, R, NT> );
}

struct Item<'a, S: 'a, R: Rule<'a, Symbol=S>, NT> {
    lhs: &'a NT,
    rule: &'a R,
    dot: usize,
    from: usize,
}

impl<'a, S, R, NT> gen!(Item) 
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


struct StateSet<'a, S: 'a, R: Rule<'a, Symbol=S>, NT> (Vec<gen!(Item)>);

impl<'a, S, R, NT> gen!(StateSet) 
where R: Rule<'a, Symbol=S>, S: 'a
{
    fn new() -> Self { Self (Vec::new()) }

    fn push(&mut self, item: gen!(Item)) {
        self.0.push(item);
    }

    fn merge(&mut self, mut other: Self) {
        self.0.append(&mut other.0);
    }

    fn iter(&self) -> impl Iterator<Item=&gen!(Item)> {
        self.0.iter()
    }
}

struct Chart<'a, S: 'a, R: Rule<'a, Symbol=S>, NT> (Vec<gen!(StateSet)>);

impl<'a, S, R, NT> gen!(Chart) 
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

struct Parser<'a, G, S: 'a, R, NT: 'a>
where R: Rule<'a, Symbol=S>, G: Grammar<'a, NonTerminal=NT, Rule=R>
{
    grammar: &'a G,
    chart: gen!(Chart),
    progress: usize,
}

impl<'a, G, S: 'a, R, NT: 'a, T> Parser<'a, G, S, R, NT> 
where R: Rule<'a, Symbol=S>,
      G: Grammar<'a, NonTerminal=NT, Rule=R>,
      S: Symbol<Terminal=T, NonTerminal=NT>,
      NT: Eq, T: Eq
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

    fn scan(&self, item: &gen!(Item), next_set: &mut gen!(StateSet)) {
        next_set.push(item.advance());
    }

    fn complete(&self, item: &gen!(Item), next_set: &mut gen!(StateSet)) {
        assert!(item.done());
        let from = item.from;
        for old_item in self.chart.get(from).iter() {
            if let Some(sym) = old_item.dot_symbol() {
                if let Some(nt) = sym.nonterminal() {
                    if nt == item.lhs {
                        next_set.push(old_item.advance());
                    }
                }
            }
        }
    }

    fn parse_token(&mut self, token: T) {
        let mut next_set = StateSet::new();

        for item in self.chart.get(self.progress).iter() {
            if let Some(symbol) = item.dot_symbol() {
                symbol.call_match(
                    |nt| {
                        //self.predict();
                    },
                    |t| {
                        if t == &token {
                            self.scan(item, &mut next_set);
                        }
                    }
                );
            } else {
                self.complete(item, &mut next_set);
            }
        }
        self.chart.push(next_set);
        self.progress += 1;
    }
}
