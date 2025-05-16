
from collections import defaultdict, deque

class LR0Item:
    def __init__(self, head, body, dot_pos):
        self.head = head
        self.body = body
        self.dot_pos = dot_pos

    def __eq__(self, other):
        return (self.head == other.head and self.body == other.body and self.dot_pos == other.dot_pos)

    def __hash__(self):
        return hash((self.head, tuple(self.body), self.dot_pos))

    def is_reduce_item(self):
        return self.dot_pos == len(self.body)

    def next_symbol(self):
        return self.body[self.dot_pos] if self.dot_pos < len(self.body) else None

    def advance(self):
        return LR0Item(self.head, self.body, self.dot_pos + 1)

    def __str__(self):
        before = ' '.join(self.body[:self.dot_pos])
        after = ' '.join(self.body[self.dot_pos:])
        return f"{self.head} -> {before} • {after}"


class Grammar:
    def __init__(self):
        self.productions = defaultdict(list)
        self.terminals = set()
        self.non_terminals = set()
        self.start_symbol = None
        self.first = defaultdict(set)
        self.follow = defaultdict(set)
        self.action_table = {}
        self.goto_table = {}
        self.states = []
        self.has_slr_conflict = False  # Track SLR(1) conflicts

    def add_production(self, head, body_str):
        body = body_str.strip().split()
        if self.start_symbol is None:
            self.start_symbol = head
        self.productions[head].append(body)
        self.non_terminals.add(head)
        for symbol in body:
            if not symbol.isupper() and symbol != 'e':
                self.terminals.add(symbol)
            elif symbol != head:
                self.non_terminals.add(symbol)

    def first_of_string(self, symbols):
        if not symbols:
            return {'e'}
        result = set()
        for symbol in symbols:
            if symbol not in self.productions:
                result.add(symbol)
                break
            result |= self.first[symbol] - {'e'}
            if 'e' not in self.first[symbol]:
                break
        else:
            result.add('e')
        return result

    def calculate_first(self):
        changed = True
        while changed:
            changed = False
            for head in self.productions:
                for body in self.productions[head]:
                    for symbol in body:
                        if symbol not in self.productions:
                            if symbol not in self.first[head]:
                                self.first[head].add(symbol)
                                changed = True
                            break
                        before = len(self.first[head])
                        self.first[head] |= self.first[symbol] - {'e'}
                        if 'e' not in self.first[symbol]:
                            break
                        if symbol == body[-1]:
                            self.first[head].add('e')
                        changed |= len(self.first[head]) > before

    def calculate_follow(self):
        self.follow[self.start_symbol].add('$')
        changed = True
        while changed:
            changed = False
            for head, bodies in self.productions.items():
                for body in bodies:
                    for i, B in enumerate(body):
                        if B in self.productions:
                            beta = body[i+1:]
                            trailer = self.first_of_string(beta) - {'e'}
                            if trailer - self.follow[B]:
                                self.follow[B] |= trailer
                                changed = True
                            if 'e' in self.first_of_string(beta) or not beta:
                                if self.follow[head] - self.follow[B]:
                                    self.follow[B] |= self.follow[head]
                                    changed = True

    def augmented(self):
        new = Grammar()
        new.start_symbol = self.start_symbol + "'"
        new.productions = self.productions.copy()
        new.terminals = self.terminals.copy()
        new.non_terminals = self.non_terminals.copy()
        new.add_production(new.start_symbol, self.start_symbol)
        return new

    def closure(self, items):
        closure_set = set(items)
        added = True
        while added:
            added = False
            new_items = set()
            for item in closure_set:
                next_sym = item.next_symbol()
                if next_sym and next_sym in self.productions:
                    for prod in self.productions[next_sym]:
                        new_item = LR0Item(next_sym, prod, 0)
                        if new_item not in closure_set:
                            new_items.add(new_item)
                            added = True
            closure_set |= new_items
        return frozenset(closure_set)

    def goto(self, items, symbol):
        moved = set()
        for item in items:
            if item.next_symbol() == symbol:
                moved.add(item.advance())
        return self.closure(moved)

    def build_lr0_states(self):
        augmented = self.augmented()
        start = LR0Item(augmented.start_symbol, [self.start_symbol], 0)
        start_closure = augmented.closure([start])
        states = [start_closure]
        transitions = {}
        seen = {start_closure: 0}
        queue = deque([start_closure])

        while queue:
            current = queue.popleft()
            idx = seen[current]
            for symbol in self.terminals | self.non_terminals:
                target = self.goto(current, symbol)
                if not target:
                    continue
                if target not in seen:
                    seen[target] = len(states)
                    states.append(target)
                    queue.append(target)
                transitions[(idx, symbol)] = seen[target]
        self.states = states
        return transitions

    def build_slr_tables(self):
        self.calculate_first()
        self.calculate_follow()
        transitions = self.build_lr0_states()
        action = defaultdict(dict)
        goto = defaultdict(dict)
        augmented = self.augmented()
        for idx, state in enumerate(self.states):
            for item in state:
                if item.is_reduce_item():
                    if item.head == augmented.start_symbol:
                        action[idx]['$'] = ('accept',)
                    else:
                        for a in self.follow[item.head]:
                            if a in action[idx] and action[idx][a] != ('reduce', item.head, item.body):
                                print(f"SLR(1) conflict at state {idx} on symbol '{a}': existing {action[idx][a]} vs new reduce")
                                self.has_slr_conflict = True
                            action[idx][a] = ('reduce', item.head, item.body)

                else:
                    sym = item.next_symbol()
                    target = self.goto(state, sym)
                    if target in self.states:
                        tidx = self.states.index(target)
                        if sym in self.terminals:
                            if sym in action[idx] and action[idx][sym] != ('shift', tidx):
                                print(f"SLR(1) conflict at state {idx} on symbol '{sym}': existing {action[idx][sym]} vs new shift")
                                self.has_slr_conflict = True
                            action[idx][sym] = ('shift', tidx)

                        else:
                            goto[idx][sym] = tidx
        if self.has_slr_conflict:
            print("Grammar is not SLR(1): conflicts detected.")
            self.action_table = {}
            self.goto_table = {}
            return None, None

        self.action_table = action
        self.goto_table = goto
        return action, goto


    def build_ll1_table(self):
        self.calculate_first()
        self.calculate_follow()
        ll1_table = defaultdict(dict)
        for head, prods in self.productions.items():
            for body in prods:
                first = self.first_of_string(body)
                for terminal in first - {'e'}:
                    if terminal in ll1_table[head]:
                        return None  # Conflicto LL(1)
                    ll1_table[head][terminal] = body
                if 'e' in first:
                    for terminal in self.follow[head]:
                        if terminal in ll1_table[head]:
                            return None  # Conflicto LL(1)
                        ll1_table[head][terminal] = body
        return ll1_table


def slr_parse(tokens, grammar):
    stack = [0]
    tokens = tokens + ['$']
    idx = 0
    while True:
        state = stack[-1]
        current = tokens[idx]
        if current not in grammar.action_table[state]:
            return False
        action = grammar.action_table[state][current]
        if action[0] == 'shift':
            stack.append(action[1])
            idx += 1
        elif action[0] == 'reduce':
            _, head, body = action
            for _ in body:
                stack.pop()
            top = stack[-1]
            stack.append(grammar.goto_table[top][head])
        elif action[0] == 'accept':
            return True
        else:
            return False


def parse_ll1(tokens, grammar, table):
    stack = ['$', grammar.start_symbol]
    tokens = tokens + ['$']
    idx = 0
    while stack:
        top = stack.pop()
        current = tokens[idx]
        if top == current:
            if top == '$':
                return True
            idx += 1
        elif top not in grammar.productions:
            return False
        elif current in table[top]:
            production = table[top][current]
            if production != ['e']:
                stack.extend(reversed(production))
        else:
            return False
    return False


def main():
    print("Ingrese el número de reglas de la gramática:")
    n = int(input())
    grammar = Grammar()
    print("Ingrese las reglas, ejemplo: E->E + T | T")
    for _ in range(n):
        line = input().strip()
        if '->' not in line:
            continue
        left, right = line.split('->', 1)
        left = left.strip()
        alternatives = right.split('|')
        for alt in alternatives:
            cleaned = ' '.join(alt.strip().split())
            grammar.add_production(left, cleaned)

    grammar.build_slr_tables()
    ll1_table = grammar.build_ll1_table()
    is_ll = ll1_table is not None

    print("Gramática cargada con las siguientes producciones:")
    for head, bodies in grammar.productions.items():
        for body in bodies:
            print(f"  {head} -> {' '.join(body)}")

    if is_ll and grammar.action_table:
        tipo = "LL(1) y SLR(1)"
    elif is_ll:
        tipo = "LL(1)"
    elif grammar.action_table:
        tipo = "SLR(1)"
    else:
        tipo = "ninguna (no válida)"

    print(f"Tipo de gramática detectado: {tipo}")

    if tipo == "ninguna (no válida)":
        print("No se puede analizar cadenas con esta gramática.")
        return

    usar_ll = False
    if is_ll and grammar.action_table:
        while True:
            print("¿Deseas usar el parser LL(1) o SLR(1)?")
            resp = input("Escribe 'LL' o 'SLR': ").strip().upper()
            if resp == "LL":
                usar_ll = True
                break
            elif resp == "SLR":
                usar_ll = False
                break
            else:
                print("Opción no válida. Escribe 'LL' o 'SLR'.")
    elif is_ll:
        usar_ll = True
    elif grammar.action_table:
        usar_ll = False
    else:
        print("No se puede analizar cadenas con esta gramática.")
        return



    print("Ahora puedes ingresar cadenas para analizar (usa espacios entre símbolos):")
    while True:
        line = input(">> ")
        if not line.strip():
            break
        tokens = line.strip().split()
        if usar_ll:
            result = parse_ll1(tokens, grammar, ll1_table)
        else:
            result = slr_parse(tokens, grammar)
        print("yes" if result else "no")


if __name__ == "__main__":
    main()
