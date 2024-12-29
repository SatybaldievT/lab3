use lazy_static::lazy_static;
use rand::seq::IteratorRandom;
use regex::Regex;
use std::collections::btree_map::Values;
use std::collections::{HashMap, HashSet, VecDeque};
use std::error::Error;
use rand::Rng;
use serde::{Deserialize, Serialize};
use std::{char, fs, string};

#[derive(Serialize)]
struct WordCheckResult {
    word: String,
    in_language: bool,
}

#[derive(Debug, PartialEq, Clone)]
enum TokenType {
    NT,    // Non-terminal
    T,     // Terminal
    ARROW, // Arrow "->"
    EOL,   // End of line
    BLANK, // Whitespace
}
lazy_static! {
    static ref REGEXPS: Vec<(TokenType, Regex)> = vec![
        (
            TokenType::NT,
            Regex::new(r"^[A-Z][0-9]?|\[[A-Za-z]+[0-9]*\]").unwrap()
        ),
        (TokenType::T, Regex::new(r"^[a-z]").unwrap()),
        (TokenType::ARROW, Regex::new(r"^->").unwrap()),
        (TokenType::EOL, Regex::new(r"^[\r\n|\n]+").unwrap()),
        (TokenType::BLANK, Regex::new(r"^[ |\t]+").unwrap()),
    ];
}

#[derive(Debug, PartialEq)]
struct Token {
    token_type: TokenType,
    value: String,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
struct Term(String);

impl Term {
    fn new(input: &str) -> Option<Self> {
        let term_regex = Regex::new(r"^[a-z]$").unwrap();
        if term_regex.is_match(input) {
            Some(Self(input.to_string()))
        } else {
            None
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
struct NonTerm(String);

impl NonTerm {
    fn new(input: &str) -> Option<Self> {
        let nonterm_regex = Regex::new(r"^[A-Z][0-9]?$|^\[[A-Za-z]+[0-9]*\]$").unwrap();
        if nonterm_regex.is_match(input) {
            Some(Self(input.to_string()))
        } else {
            None
        }
    }
}

fn tokenize(input: &str) -> Result<Vec<Token>, Box<dyn Error>> {
    let mut tokens = Vec::new();
    let mut pos = 0;

    while pos < input.len() {
        let mut found = false;

        for (token_type, re) in REGEXPS.iter() {
            if let Some(mat) = re.find(&input[pos..]) {
                if mat.start() == 0 {
                    let match_str = mat.as_str().to_string();
                    pos += match_str.len();
                    found = true;

                    if *token_type != TokenType::BLANK {
                        tokens.push(Token {
                            token_type: token_type.clone(),
                            value: match_str,
                        });
                    }
                    break;
                }
            }
        }

        if !found {
            return Err(format!(
                "Unexpected character '{}' at position {}",
                input.chars().nth(pos).unwrap(),
                pos
            )
            .into());
        }
    }

    Ok(tokens)
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
struct Alternative(Vec<Symbol>);

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
enum Symbol {
    Term(Term),
    NonTerm(NonTerm),
}
impl Symbol {
    // Метод для проверки, является ли символ терминалом
    pub fn is_term(&self) -> bool {
        match self {
            Symbol::Term(_) => true,     // Если это терминал, возвращаем true
            Symbol::NonTerm(_) => false, // Если это нетерминал, возвращаем false
        }
    }
    pub fn term(&self) -> Term {
        match self {
            Symbol::Term(value) => value.clone(), // Если это терминал, возвращаем true
            Symbol::NonTerm(_) => EPS.clone(),    // Если это нетерминал, возвращаем false
        }
    }
    pub fn nonTerm(&self) -> NonTerm {
        match self {
            Symbol::Term(_) => NonTerm("".to_string()), // Если это терминал, возвращаем true
            Symbol::NonTerm(value) => value.clone(),    // Если это нетерминал, возвращаем false
        }
    }
}

impl Alternative {
    fn new(value: Vec<Symbol>) -> Self {
        Alternative(value)
    }
}
lazy_static! {
    static ref EPS: Term = Term("".to_string()); // Пустой терминальный символ
    static ref EPS_RULE: Alternative = Alternative(vec![Symbol::Term(EPS.clone())]); // Правило для пустого символа
}
#[derive(Debug,Clone)]
pub struct CFG {
    sigma: HashSet<Term>,
    n: HashSet<NonTerm>,
    s: NonTerm,
    p: HashMap<NonTerm, HashSet<Alternative>>,
}
impl CFG {
    pub fn new() -> Self {
        CFG {
            sigma: HashSet::new(),
            n: HashSet::new(),
            s: NonTerm("".to_string()), // Пустой стартовый символ
            p: HashMap::new(),
        }
    }
    pub fn delete_long_rules(&mut self) {
        let mut rules_to_delete = Vec::new();
        let mut new_productions = Vec::new(); // Для хранения новых правил

        // Проходим по всем правилам грамматики
        for (nt, alts) in self.p.clone() {
            for rule in alts {
                let rule_length = rule.0.len();
                if rule_length <= 2 {
                    continue; // Пропускаем короткие правила
                }

                // Запоминаем правила, которые нужно удалить
                rules_to_delete.push((nt.clone(), rule.clone()));

                let mut index = 1;
                let mut new_nonterms = Vec::new();

                // Создаем новые нетерминалы
                for _ in 1..rule_length - 1 {
                    let mut new_nt = NonTerm(format!("[Long{}{}]", nt.0, index));

                    // Проверяем на возможные коллизии имён
                    while self.n.contains(&new_nt) {
                        index += 1;
                        new_nt = NonTerm(format!("[Long{}{}]", nt.0, index));
                    }

                    new_nonterms.push(new_nt.clone());
                    self.p.insert(new_nt.clone(), HashSet::new()); // Добавляем новый нетерминал в грамматику
                    index += 1;
                }

                // Добавляем новые нетерминалы в множество N
                for new_nt in &new_nonterms {
                    self.n.insert(new_nt.clone());
                }

                // Формируем продукцию для первого нетерминала
                let rule = &rule.0;
                let first_symbol = &rule[0];

                // Формируем продукцию для первого нетерминала
                new_productions.push((
                    nt.clone(),
                    Alternative(vec![
                        match first_symbol {
                            Symbol::Term(t) => Symbol::Term(t.clone()), // Если символ термина
                            Symbol::NonTerm(nt) => Symbol::NonTerm(nt.clone()), // Если символ нетермина
                        },
                        Symbol::NonTerm(new_nonterms[0].clone()), // Следующий символ — новый нетерминал
                    ]),
                ));

                // Формируем промежуточные продукции
                for i in 0..rule_length - 3 {
                    let curr_symbol = &rule[i + 1];
                    let next_symbol = &new_nonterms[i + 1];
                    new_productions.push((
                        new_nonterms[i].clone(),
                        Alternative(vec![
                            match curr_symbol {
                                Symbol::Term(t) => Symbol::Term(t.clone()),
                                Symbol::NonTerm(nt) => Symbol::NonTerm(nt.clone()),
                            },
                            Symbol::NonTerm(next_symbol.clone()),
                        ]),
                    ));
                }

                // Формируем последнюю продукцию
                let second_last_symbol = &rule[rule_length - 2];
                let last_symbol = &rule[rule_length - 1];
                new_productions.push((
                    new_nonterms[rule_length - 3].clone(),
                    Alternative(vec![
                        match second_last_symbol {
                            Symbol::Term(t) => Symbol::Term(t.clone()),
                            Symbol::NonTerm(nt) => Symbol::NonTerm(nt.clone()),
                        },
                        match last_symbol {
                            Symbol::Term(t) => Symbol::Term(t.clone()),
                            Symbol::NonTerm(nt) => Symbol::NonTerm(nt.clone()),
                        },
                    ]),
                ));
            }
        }

        // Применяем новые продукции
        for (nt, alt) in new_productions {
            self.p.entry(nt).or_insert_with(HashSet::new).insert(alt);
        }

        // Удаляем длинные правила
        for (nt, rule) in rules_to_delete {
            if let Some(alts) = self.p.get_mut(&nt) {
                alts.remove(&Alternative(rule.0));
            }
        }
    }
    pub fn delete_chain_rules(&mut self) {
        let mut has_chain_to: HashMap<NonTerm, HashSet<NonTerm>> = HashMap::new();
        for nt in self.n.iter().clone() {
            let mut reachable = HashSet::new();
            let mut next_reachable = HashSet::new();
            reachable.insert(nt.clone());
            // Step 1: Find all direct chain rules for this non-terminal
            for (B, alts) in self.p.clone() {
                if alts
                    .clone()
                    .contains(&Alternative(vec![Symbol::NonTerm(nt.clone())]))
                {
                    reachable.insert(B.clone());
                }
            }

            for (C, alts) in self.p.clone() {
                if (has_chain_to.get(nt).is_some()) {
                    for D in has_chain_to.get(nt).unwrap().clone() {
                        if alts
                            .clone()
                            .contains(&Alternative(vec![Symbol::NonTerm(D.clone())]))
                        {
                            next_reachable.insert(C.clone());
                        }
                    }
                }
            }
            next_reachable.union(&reachable.clone());
            println!("[{:?} {:?}]", nt, reachable);
            has_chain_to.insert(nt.clone(), reachable.clone());

            // Step 2: Propagate reachability via chain rules

            while has_chain_to.get(&nt) != Some(&next_reachable) {
                // Step 2: Propagate reachability via chain rules
                for (C, alts) in self.p.clone() {
                    for D in has_chain_to.get(nt).unwrap().clone() {
                        if alts
                            .clone()
                            .contains(&Alternative(vec![Symbol::NonTerm(D.clone())]))
                        {
                            next_reachable.insert(C.clone());
                        }
                    }
                }
                next_reachable.union(&reachable.clone());
                has_chain_to.insert(nt.clone(), next_reachable.clone());
                for (C, alts) in self.p.clone() {
                    for D in has_chain_to.get(nt).unwrap().clone() {
                        if alts
                            .clone()
                            .contains(&Alternative(vec![Symbol::NonTerm(D.clone())]))
                        {
                            next_reachable.insert(C.clone());
                        }
                    }
                }
                next_reachable.union(&reachable.clone());
                //reachable = next_reachable.clone();
            }
        }

        println!("awdaw{:?}\nasd", has_chain_to);
        // Step 3: Add rules

        let mut additions: HashMap<NonTerm, HashSet<Alternative>> = HashMap::new();
        for (child_nt, parents) in &has_chain_to {
            if let Some(child_alts) = self.p.get(child_nt) {
                for parent_nt in parents {
                    if let Some(parent_alts) = self.p.get(parent_nt) {
                        let mut new_alts = additions
                            .entry(parent_nt.clone())
                            .or_insert_with(HashSet::new);
                        // Добавляем все альтернативы из дочернего нетерминала к родительскому
                        for alt in child_alts {
                            println!("{:?} {:?}", parent_nt, alt.clone());
                            new_alts.insert(alt.clone());
                        }
                    }
                }
            }
        }

        // 3. Применяем добавления
        for (parent_nt, alts) in additions {
            if let Some(parent_alts) = self.p.get_mut(&parent_nt) {
                for alt in alts {
                    parent_alts.insert(alt);
                }
            }
        }
        // Step 4: Delete chain rules
        for (_, alternatives) in self.p.iter_mut() {
            alternatives.retain(|alt| {
                // Retain only those alternatives where the RHS is not a single non-terminal
                if alt.0.len() == 1 {
                    if let Symbol::NonTerm(_) = alt.0[0] {
                        false // This is a chain rule, so remove it
                    } else {
                        true // Keep if it's not a chain rule
                    }
                } else {
                    true // Keep if it's not a chain rule
                }
            });
        }
    }
    pub fn delete_unreachable(&mut self) {
        let mut reachable: HashSet<NonTerm> = HashSet::new();
        let mut stack: VecDeque<NonTerm> = VecDeque::new();
        stack.push_back(self.s.clone());
        reachable.insert(self.s.clone());

        while let Some(nt) = stack.pop_front() {
            if let Some(alternatives) = self.p.get(&nt) {
                for alt in alternatives {
                    for symbol in &alt.0 {
                        if let Symbol::NonTerm(ref nonterm) = symbol {
                            if !reachable.contains(nonterm) {
                                reachable.insert(nonterm.clone());
                                stack.push_back(nonterm.clone());
                            }
                        }
                    }
                }
            }
        }

        self.n.retain(|nt| reachable.contains(nt));
        self.p.retain(|nt, _| reachable.contains(nt));
    }
    /// Удаление негенерирующих символов
    pub fn delete_nongenerating(&mut self) {
        let mut generating: HashSet<NonTerm> = HashSet::new();
        let mut changed = true;

        while changed {
            changed = false;

            for (nt, alternatives) in &self.p {
                if generating.contains(nt) {
                    continue;
                }

                for alt in alternatives {
                    if alt.0.iter().all(|symbol| match symbol {
                        Symbol::Term(_) => true,
                        Symbol::NonTerm(nt) => generating.contains(nt),
                    }) {
                        generating.insert(nt.clone());
                        changed = true;
                        break;
                    }
                }
            }
        }

        self.n.retain(|nt| generating.contains(nt));
        self.p.retain(|nt, _| generating.contains(nt));
    }
    /// Удаление бесполезных символов (недостижимых и негенерирующих)
    pub fn delete_useless(&mut self) {
        self.delete_nongenerating();
        self.delete_unreachable();
    }
    pub fn chomskiy_normalize(&mut self) {
        let mut term_to_nonterm: HashMap<Term, NonTerm> = HashMap::new();
        let mut index: usize = 0;

        // Шаг 1: Заменяем терминалы на нетерминалы
        for t in &self.sigma {
            let mut nt = NonTerm(format!("[{}NT]", t.0));
            while self.n.contains(&nt) {
                index += 1;
                nt = NonTerm(format!("[{}NT{}]", t.0, index));
            }
            self.n.insert(nt.clone());
            term_to_nonterm.insert(t.clone(), nt);
        }

        for (_, alts) in self.p.iter_mut() {
            // Используем `iter_mut()` для изменения содержимого
            for mut rule in alts.clone().iter() {
                // Используем `iter_mut()` для получения изменяемой ссылки на каждый `rule`

                let mut rule1 = rule.clone();
                alts.remove(rule);
                if rule1.0.len() == 2 {
                    let a = rule.0[1].term();
                    if rule1.0[1].is_term() {
                        // Теперь можем изменять `rule.0[1]`
                        rule1.0[1] = Symbol::NonTerm(term_to_nonterm.get(&a).unwrap().clone());
                    }
                    let b = rule.0[0].term();
                    if rule1.0[0].is_term() {
                        // Теперь можем изменять `rule.0[1]`
                        rule1.0[0] = Symbol::NonTerm(term_to_nonterm.get(&b).unwrap().clone());
                    }
                }
                rule = &rule1;
                alts.insert(rule.clone());
            }
        }

        // Шаг 3: Добавляем правила для новых нетерминалов
        for (t, nt) in term_to_nonterm {
            self.p
                .entry(nt)
                .or_insert_with(HashSet::new)
                .insert(Alternative(vec![Symbol::Term(t)]));
        }
    }
    pub fn construct_first(&mut self) -> HashMap<NonTerm, HashSet<Term>> {
        let mut first: HashMap<NonTerm, HashSet<Term>> = HashMap::new();
        for i in self.n.clone() {
            let hc: HashSet<Term> = HashSet::new();
            first.insert(i, hc);
        }
        let mut changed = true;
        while changed {
            changed = false;
            for (A, rules) in self.p.clone() {
                for rule in rules.iter() {
                    if rule.0[0].is_term() {
                        let old = first.clone();
                        first.get_mut(&A).unwrap().insert(rule.0[0].clone().term());

                        if !old.eq(&first) {
                            changed = true
                        }
                    } else {
                        let mut old = first.clone();
                        //println!("{} {}", A.0, rule.0[0].nonTerm().0);
                        for i in old.get(&rule.0[0].clone().nonTerm()).unwrap().iter() {
                            first.get_mut(&A).unwrap().insert(i.clone());
                        }
                        if !old.eq(&first) {
                            changed = true;
                            //println!("Fuck");
                        }
                    }
                }
            }
        }
        first
    }
    pub fn follow(&mut self, first: HashMap<NonTerm, HashSet<Term>>) -> HashMap<NonTerm, HashSet<Term>> {
        let mut follow: HashMap<NonTerm, HashSet<Term>> = HashMap::new();
        
        // Инициализация follow множеств
        for nt in self.n.clone() {
            follow.insert(nt, HashSet::new());
        }
        follow
            .get_mut(&self.s)
            .unwrap()
            .insert(Term("$".to_string())); // Добавляем $ для стартового символа
        
        let mut changed = true;
        while changed {
            changed = false;
            
            for (A, rules) in self.p.clone() {
                for rule in rules.iter() {
                    let len = rule.0.len();
                    assert!(len == 2 || len == 1, "НФХ допускает только правила вида A -> BC или A -> a");
    
                    if len == 2 {
                        // Обрабатываем правило A -> BC
                        let B = rule.0[0].nonTerm();
                        let C = rule.0[1].nonTerm();
    
                        // Добавляем first(C) (без ε) в follow(B)
                        let old_follow = follow.clone();
                        for term in first.get(&C).unwrap() {
                            follow.get_mut(&B).unwrap().insert(term.clone());
                        }
                        if old_follow != follow {
                            changed = true;
                        }
    
                        // Если C может быть пустым, добавляем follow(A) в follow(B)
                        if first.get(&C).unwrap().contains(&Term("ε".to_string())) {
                            let old_follow = follow.clone();
                            for term in follow.clone().get(&A).unwrap() {
                                follow.get_mut(&B).unwrap().insert(term.clone());
                            }
                            if old_follow != follow {
                                changed = true;
                            }
                        }
                    } else if len == 1 {
                        // Правило A -> a не влияет на follow, пропускаем
                        continue;
                    }
                }
            }
        }
        
        follow
    }
    pub fn reverse(&self) -> CFG {
        let mut reversed_p: HashMap<NonTerm, HashSet<Alternative>> = HashMap::new();

        for (nt, alts) in &self.p {
            let reversed_alts: HashSet<Alternative> = alts
                .iter()
                .map(|alt| Alternative(alt.0.iter().rev().cloned().collect()))
                .collect();
            reversed_p.insert(nt.clone(), reversed_alts);
        }

        CFG {
            sigma: self.sigma.clone(),
            n: self.n.clone(),
            s: self.s.clone(), // Стартовый символ остаётся прежним
            p: reversed_p,
        }
    }
    // Получение last-множества
    pub fn last_sets(&mut self, reversed: bool) -> HashMap<NonTerm, HashSet<Term>> {
        if reversed {
            self.construct_first()
        } else {
            let mut reversed_g = self.reverse();
            reversed_g.construct_first()
        }
    }
    // Получение precede-множества
    pub fn precede_sets(
        &mut self,
        reversed: bool,
        last: Option<HashMap<NonTerm, HashSet<Term>>>,
    ) -> HashMap<NonTerm, HashSet<Term>> {
        let last_sets = last.unwrap_or(self.last_sets(reversed));
        let mut reversed_g = if reversed { self.clone() } else { self.reverse() };
        reversed_g.follow(last_sets)
    }
    // Получение bigram-матрицы
    pub fn get_bigram_matrix(
        &mut self,
        first: Option<HashMap<NonTerm, HashSet<Term>>>,
        follow: Option<HashMap<NonTerm, HashSet<Term>>>,
        last: Option<HashMap<NonTerm, HashSet<Term>>>,
        precede: Option<HashMap<NonTerm, HashSet<Term>>>,
    ) -> HashMap<(Term, Term), bool> {
        let first_sets = first.unwrap_or(self.construct_first());
        let follow_sets = follow.unwrap_or( self.follow(first_sets.clone()));
        let mut reversed_g = self.reverse();
        let last_sets = last.unwrap_or( reversed_g.last_sets(true));
        let precede_sets = precede.unwrap_or(reversed_g.precede_sets(true, Some(last_sets.clone())));

        let all_rules: Vec<Vec<Symbol>> = self
            .p
            .values()
            .flat_map(|alts| alts.iter().map(|alt| alt.0.clone()))
            .collect();

        let mut bigram_matrix = HashMap::new();

        for y1 in &self.sigma {
            for y2 in &self.sigma {
                let condition1 = all_rules.iter().any(|r| {
                    r.windows(2).any(|pair| {
                        matches!((&pair[0], &pair[1]), (Symbol::Term(t1), Symbol::Term(t2)) if t1 == y1 && t2 == y2)
                    })
                });

                let condition2 = self.n.iter().any(|nt| {
                    last_sets.get(nt).map_or(false, |set| set.contains(y1))
                        && follow_sets.get(nt).map_or(false, |set| set.contains(y2))
                });

                let condition3 = self.n.iter().any(|nt| {
                    precede_sets.get(nt).map_or(false, |set| set.contains(y1))
                        && first_sets.get(nt).map_or(false, |set| set.contains(y2))
                });

                let condition4 = self
                    .n
                    .iter()
                    .flat_map(|a| self.n.iter().map(move |b| (a, b)))
                    .any(|(p1, p2)| {
                        last_sets.get(p1).map_or(false, |set| set.contains(y1))
                            && first_sets.get(p2).map_or(false, |set| set.contains(y2))
                            && follow_sets.get(p1).map_or(false, |set| set.contains(y2))
                    });

                bigram_matrix.insert((y1.clone(), y2.clone()), condition1 || condition2 || condition3 || condition4);
            }
        }

        bigram_matrix
    }
    // Генерация случайного слова
    pub fn some_word(
        &mut self,
        first: Option<HashMap<NonTerm, HashSet<Term>>>,
        follow: Option<HashMap<NonTerm, HashSet<Term>>>,
        last: Option<HashMap<NonTerm, HashSet<Term>>>,
        precede: Option<HashMap<NonTerm, HashSet<Term>>>,
        length_upperbound: usize,
        random_term_probability: f64,
        terminating_probability: f64,
    ) -> Vec<Term> {
        let first_sets = first.unwrap_or( self.construct_first());
        let last_sets = last.unwrap_or( self.last_sets(false));
        let bigram_matrix = self.get_bigram_matrix(
            Some(first_sets.clone()),
            follow,
            Some(last_sets.clone()),
            precede,
        );

        let start_terminals: Vec<&Term> = first_sets.get(&self.s).unwrap().iter().collect();
        let last_terminals: HashSet<&Term> = last_sets.get(&self.s).unwrap().iter().clone().collect();

        let mut word = Vec::new();
        let mut current = start_terminals[rand::random::<usize>() % start_terminals.len()].clone();
        word.push(current.clone());

        while word.len() < length_upperbound {
            let next_variants: Vec<&Term> = if rand::random::<f64>() < random_term_probability {
                self.sigma.iter().collect()
            } else {
                self.sigma
                    .iter()
                    .filter(|c| bigram_matrix.get(&(current.clone(), (*c).clone())).cloned().unwrap_or(false))
                    .collect()
            };

            if next_variants.is_empty() {
                break;
            }

            let next = next_variants[rand::random::<usize>() % next_variants.len()].clone();
            word.push(next.clone());
            if last_terminals.contains(&next) && rand::random::<f64>() < terminating_probability {
                break;
            }
            current = next;
        }

        word
    }
    // Генерация слова из правил
    pub fn get_word(&self) -> Vec<Term> {
        let mut stack = Vec::new();
        let mut word = Vec::new();
        let mut terms_only_rules = HashMap::new();
        let mut rules_with_nonterms = HashMap::new();

        for (nt, alts) in &self.p {
            terms_only_rules.insert(
                nt.clone(),
                alts.iter()
                    .filter(|a| a.0.iter().all(|x| matches!(x, Symbol::Term(_))))
                    .cloned()
                    .collect::<HashSet<Alternative>>(),
            );
            rules_with_nonterms.insert(
                nt,
                 alts.iter()
                 .filter(|a| a.0.iter().any(|x| matches!(x, Symbol::NonTerm(_))))
                 .cloned()
                 .collect::<HashSet<Alternative>>()
                );
        }

        let mut term_only_probability = 0.0;
        let probability_step = 0.05;
        stack.push(Symbol::NonTerm(self.s.clone()));

        while let Some(sym) = stack.pop() {
            match sym {
                Symbol::Term(t) => word.push(t),
                Symbol::NonTerm(nt) => {
                    let rule = if terms_only_rules.get(&nt).unwrap().is_empty() {
                        rules_with_nonterms.get(&nt).unwrap().iter().choose(&mut rand::thread_rng()).unwrap()
                    } else if rules_with_nonterms.get(&nt).unwrap().is_empty() {
                        terms_only_rules.get(&nt).unwrap().iter().choose(&mut rand::thread_rng()).unwrap()
                    } else if rand::random::<f64>() < term_only_probability {
                        terms_only_rules.get(&nt).unwrap().iter().choose(&mut rand::thread_rng()).unwrap()
                    } else {
                        rules_with_nonterms.get(&nt).unwrap().iter().choose(&mut rand::thread_rng()).unwrap()
                    };

                    stack.extend(rule.0.iter().cloned());
                    term_only_probability += probability_step;
                }
            }
        }

        word.reverse();
        word
    }
    }

pub fn parse_cfg(tokens: &mut Vec<Token>) -> Result<CFG, String> {
    let mut pos = 0;
    let mut rules = Vec::new();
    let mut nonterms = HashSet::new();
    let mut terms = HashSet::new();
    let mut start: Option<NonTerm> = None;

    // Parsing non-terminal
    fn parse_nt(
        pos: &mut usize,
        tokens: &Vec<Token>,
        nonterms: &mut HashSet<NonTerm>,
        start: &mut Option<NonTerm>,
    ) -> Result<NonTerm, String> {
        if tokens[*pos].token_type == TokenType::NT {
            let nt = NonTerm(tokens[*pos].value.clone());
            nonterms.insert(nt.clone());
            if start.is_none() {
                *start = Some(nt.clone());
            }
            *pos += 1;
            Ok(nt)
        } else {
            Err(format!(
                "Expected NonTerm, found {:?}",
                tokens[*pos].token_type
            ))
        }
    }

    // Parsing terminal
    fn parse_t(
        pos: &mut usize,
        tokens: &Vec<Token>,
        terms: &mut HashSet<Term>,
    ) -> Result<Term, String> {
        if tokens[*pos].token_type == TokenType::T {
            let t = Term(tokens[*pos].value.clone());
            terms.insert(t.clone());
            *pos += 1;
            Ok(t)
        } else {
            Err(format!(
                "Expected Term, found {:?}",
                tokens[*pos].token_type
            ))
        }
    }

    // Parsing arrow
    fn parse_arrow(pos: &mut usize, tokens: &Vec<Token>) -> Result<(), String> {
        if tokens[*pos].token_type == TokenType::ARROW {
            *pos += 1;
            Ok(())
        } else {
            Err(format!(
                "Expected Arrow, found {:?}",
                tokens[*pos].token_type
            ))
        }
    }

    // Parsing end of line
    fn parse_eol(pos: &mut usize, tokens: &Vec<Token>) -> Result<(), String> {
        if tokens[*pos].token_type == TokenType::EOL {
            *pos += 1;
            Ok(())
        } else {
            Err(format!("Expected EOL, found {:?}", tokens[*pos].token_type))
        }
    }

    // Main parsing loop
    while pos < tokens.len() {
        // Parse a rule: LHS -> RHS
        let lhs = parse_nt(&mut pos, tokens, &mut nonterms, &mut start)?;
        parse_arrow(&mut pos, tokens)?;

        let mut rhs = Vec::new();
        while tokens[pos].token_type != TokenType::EOL {
            if tokens[pos].token_type == TokenType::T {
                rhs.push(Symbol::Term(parse_t(&mut pos, tokens, &mut terms)?));
            } else if tokens[pos].token_type == TokenType::NT {
                rhs.push(Symbol::NonTerm(parse_nt(
                    &mut pos,
                    tokens,
                    &mut nonterms,
                    &mut start,
                )?));
            } else {
                return Err(format!(
                    "Expected Token or NonTerm, found {:?}",
                    tokens[pos].token_type
                ));
            }
        }
        parse_eol(&mut pos, tokens)?;

        rules.push((lhs, rhs));
    }

    // Create CFG
    let mut p = HashMap::new();
    for (lhs, rhs) in rules {
        let alt = Alternative::new(rhs);
        p.entry(lhs).or_insert_with(HashSet::new).insert(alt);
    }

    if let Some(start_symbol) = start {
        Ok(CFG {
            sigma: terms,
            n: nonterms,
            s: start_symbol,
            p,
        })
    } else {
        Err("No start symbol found".to_string())
    }
}

pub fn cyk(G: &CFG, word: &[Term]) -> bool {
    let mut n = word.len();
    if (n == 0) {
        return true;
    }

    let mut nonterms: Vec<NonTerm> = G.n.clone().into_iter().collect();

    let mut nontermIndex: HashMap<NonTerm, usize> = HashMap::new();

    for i in 0..nonterms.len() {
        nontermIndex.insert(nonterms[i].clone(), i);
    }

    let mut startIndex = nontermIndex.get(&G.s).unwrap();

    let mut termToNonterms: HashMap<Term, Vec<usize>> = HashMap::new();

    let mut pairToNonterms: HashMap<(usize, usize), Vec<usize>> = HashMap::new();

    for r in G.p.clone() {
        let A = nontermIndex.get(&r.0).unwrap();
        for alt in r.1.iter() {
            if alt.0.len() == 1 && alt.0[0].is_term() {
                termToNonterms
                    .entry(alt.0[0].term())
                    .or_insert_with(Vec::new)
                    .push(*A);
            } else if (alt.0.len() == 2 && !alt.0[0].is_term() && !alt.0[1].is_term()) {
                let nt1 = alt.0[0].nonTerm();
                let nt2 = alt.0[1].nonTerm();
                let &B = nontermIndex.get(&nt1).unwrap();
                let &C = nontermIndex.get(&nt2).unwrap();

                let key = (B, C);
                pairToNonterms.entry(key).or_insert(Vec::new()).push(*A);
            } else {
                print!("WTF SMTH {} {} ", alt.0[0].is_term(), alt.0[1].is_term())
            }
        }
    }

    let mut d: Vec<Vec<Vec<bool>>> = vec![
    vec![
        vec![false; n]; n  // Размерность 1 (вектор из n элементов, все false)
    ]; nonterms.len()// Размерность 2 (вектор из n векторов, каждый из которых имеет размерность n)
];

    for i in 0..n {
        let sym = word[i].clone();
        if termToNonterms.contains_key(&sym) {
            for &A in termToNonterms.get(&sym).unwrap().into_iter() {
                d[A][i][i] = true;
            }
        }
    }

    for length in 2..=n {
        for i in 0..=n - length {
            let j = i + length - 1;
            for k in i..j {
                let mut Bs = Vec::new();
                let mut Cs = Vec::new();
                for b in 0..nonterms.len() {
                    if (d[b][i][k]) {
                        Bs.push(b)
                    };
                }
                for c in 0..nonterms.len() {
                    if (d[c][k + 1][j]) {
                        Cs.push(c)
                    };
                }

                for B in Bs.clone().iter() {
                    for C in Cs.clone().iter() {
                        let key = (*B, *C);
                        if pairToNonterms.contains_key(&key) {
                            for &A in pairToNonterms.get(&key).unwrap().iter() {
                                d[A][i][j] = true;
                            }
                        }
                    }
                }
            }
        }
    }

    return d[*startIndex][0][n - 1];
}
/*fn main1() {
    это должно быть в пост запросе на генерацию :
    const GRAMMAR: &str = "A -> a A b 
    A -> a
    ";
    let mut tokens = tokenize(GRAMMAR).unwrap();
    println!("{:?}", tokens);
    println!("");
    let mut cfg = parse_cfg(&mut tokens).ok().unwrap();

    cfg.delete_long_rules();
    println!("{:?}", cfg);
    cfg.delete_chain_rules();
    //println!("{:?}", cfg);
    cfg.delete_useless();
    //
    cfg.chomskiy_normalize();
    println!("{:?}", cfg);
    let a = Term::new("a").unwrap();
    let b = Term::new("b").unwrap();
    let V = [
        b.clone(),
        b.clone(),
        a.clone(),
        a.clone(),
        a.clone(),
    ];
    это должно быть в пост запросе на вхождение в слово  :
    println!("{:?}", cyk(&cfg.reverse(), &V));
    println!("");
    это должно быть в пост запросе на создание слов которые входят  в слово  :
    let first = cfg.construct_first();
    
    println!("{:?}", cfg.get_word());
}
 
#[post("/generate_graph")]
pub fn check_membership(&self, word: &str) -> bool {
    let word: Vec<&str> = word.chars().map(|c| c.to_string().as_str()).collect();
    self.cyk(&word)
}

pub async fn generate_graph(path: String) -> HttpResponse {

}*/
use std::sync::{Arc, Mutex};
use actix_web::http::header;
use actix_web::web::Json;
use actix_web::{get, post, HttpResponse};
static mut _cfg: Option<Arc<Mutex<CFG>>> = None;

#[derive(Deserialize)]
struct NumParam {
    num: usize,
}
#[post("/get_words")]
pub async fn get_words(_num: String) -> HttpResponse {
    let num: usize = _num.parse::<usize>().unwrap();
    let mut cfg = unsafe { _cfg.as_ref().unwrap().lock().unwrap() };
    // Генерация слов и проверка их принадлежности языку
    let results: Vec<WordCheckResult> = (0..num)
        .filter_map(|_| {
            let word = cfg.some_word(None,None,None,None,30,0., 0.5); 
            let in_language = cyk (&cfg,&word);
            Some(WordCheckResult {
                word : word.iter()
                .map(|term| term.0.clone())
                .collect(),
                in_language,
            })
        })
        .collect();
    HttpResponse::Ok().header(header::CONTENT_TYPE, "application/json").json(results)
}
#[post("/get_true_words")]
pub async fn get_true_words(_num: String) -> HttpResponse {
    let num: usize = _num.parse::<usize>().unwrap();
    let mut cfg = unsafe { _cfg.as_ref().unwrap().lock().unwrap() };
    // Генерация слов и проверка их принадлежности языку
    let results: Vec<WordCheckResult> = (0..num)
        .filter_map(|_| {
            let word = cfg.get_word(); 
            let in_language = cyk (&cfg,&word);
            Some(WordCheckResult {
                word : word.iter()
                .map(|term| term.0.clone())
                .collect(),
                in_language,
            })
        })
        .collect();
    HttpResponse::Ok().header(header::CONTENT_TYPE, "application/json").json(results)
}
fn init_gramm() {
    unsafe {
        _cfg = Some(Arc::new(Mutex::new(CFG::new())));
    }}
#[post("/set_gramm")]
pub async fn set_gramm(GRAMMAR: String) -> HttpResponse {
    let mut tokens = tokenize(&GRAMMAR).unwrap();
    println!("{:?}", tokens);
    println!("");
    let mut cfg = parse_cfg(&mut tokens).ok().unwrap();

    cfg.delete_long_rules();
    println!("{:?}", cfg);
    cfg.delete_chain_rules();
    //println!("{:?}", cfg);
    cfg.delete_useless();
    //
    cfg.chomskiy_normalize();
    println!("{:?}", cfg);
    init_gramm();
    unsafe{  *_cfg.as_ref().unwrap().lock().unwrap() = cfg
    }; 
    HttpResponse::Ok()
            .header(header::CONTENT_TYPE, "application/json")
            .body("0")
    
}