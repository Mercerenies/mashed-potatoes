#!/usr/bin/python3

from collections import defaultdict
from numbers import Number
import re
import sys


class ParseError(Exception):
    def __init__(self, string):
        super().__init__(string)

class SemanticError(Exception):
    def __init__(self, string):
        super().__init__(string)

class BCStatement(BaseException):
    pass

class Cyclic:

    def __init__(self, lst):
        self.data = lst

    def __getitem__(self, idx):
        return self.data[idx % len(self.data)]

    def __setitem__(self, idx, value):
        self.data[idx % len(self.data)] = value

labels = [
    Cyclic(["0.0f", "++i", "<>", "Object"]),
    Cyclic(["std::ignore", "nullptr", "__dict__", "void(0)"]),
    Cyclic(["$ARGV", "*read-eval*", "FS", "()"]),
]

empty_label = object()

trigger_a = Cyclic([
    ("usestrictqw/", "/;"),
    ("SETLOCAL", ""),
    ("import", ";"),
    ("CFLAGS=", ""),
    ("\emph{", "}"),
    ("`cat", "`"),
])
trigger_b = Cyclic([
    ("s/", "//g"),
    ("OUTPUT=", ""),
    ("guard", ""),
    ("lambda:", ""),
    ('"""', '"""')
])

cycles = {
    "STDERR": Cyclic(['var_a', 'var_c', 'var_e']),
    "$[": Cyclic(['var_c', 'var_e', 'var_a']),
    "`uniq-c`": Cyclic(['var_e', 'var_a', 'var_c']),
}

increments = [
    '"Hello,world!"',
    "arr[:]",
]

class Reader:

    def __init__(self, text):
        self.text = text
        self.line = 1
        self.pos  = 0
        self.state = defaultdict(lambda: 0)

    def savestate(self):
        return (self.line, self.pos)

    def loadstate(self, state):
        self.line, self.pos = state

    def skipspaces(self):
        while True:
            curr = self.text[self.pos:]
            if re.match(r"[\n\r]", curr):
                self.line += 1
                self.pos += 1
            elif re.match(r"\s", curr):
                self.pos += 1
            else:
                break

    def startswith(self, string):
        temp = self.savestate()
        for c in string:
            self.skipspaces()
            if self.pos >= len(self.text) or self.text[self.pos] != c:
                self.loadstate(temp)
                return False
            self.pos += 1
        pos = self.pos
        self.loadstate(temp)
        return pos

    def advance(self, i):
        segment = self.text[self.pos : self.pos + i]
        self.line += len(re.findall(r"[\n\r]", segment))
        self.pos += i

    def advance_to(self, i):
        segment = self.text[self.pos : i]
        self.line += len(re.findall(r"[\n\r]", segment))
        self.pos = i

    def go(self, string):
        res = self.startswith(string)
        if res: self.advance_to(res)
        return res

    def must(self, string, error = "Syntax error"):
        if not self.go(string):
            raise ParseError(error)

class LabelBinder:

    def __init__(self, label, key, value):
        self.label = label
        self.key = key
        self.value = value

    def __enter__(self):
        self.value, self.label[self.key] = self.label[self.key], self.value

    def __exit__(self, t, v, tb):
        self.value, self.label[self.key] = self.label[self.key], self.value

class LabelEnv:

    def __init__(self):
        self.content = defaultdict(lambda: None)

    def __getitem__(self, key):
        return self.content[key]

    def __setitem__(self, key, value):
        if key is not empty_label:
            self.content[key] = value

    def bind(self, key, value):
        return LabelBinder(self, key, value)

class Environment:

    def __init__(self):
        self.label = LabelEnv()
        self.var_a = 0
        self.var_c = 0
        self.var_e = 0
        self.stack = [[], [], []]

def read_label(reader):
    for c in labels:
        if reader.go(c[reader.state[c]]):
            reader.state[c] += 1
            return c
    if reader.go("t"):
        return empty_label
    raise ParseError("Label expected")

def read_op(reader):
    for curr in ['<', '>', '=']:
        if reader.go(curr):
            return curr
    raise ParseError("Operator expected")

def _cycle_expr(reader):
    for k in cycles:
        v = cycles[k]
        if reader.go(k):
            target = v[reader.state[v]]
            reader.state[v] += 1
            return lambda env: env.__dict__[target]
    return None

def _zero_expr(reader):
    if reader.go("--help"):
        return lambda env: 0
    return None

def _incr_expr(reader):
    for k in increments:
        if reader.go(k):
            value = reader.state[k]
            reader.state[k] += 1
            return lambda env: value
    return None

def _label_expr(reader):
    if reader.go("(int)"):
        label = read_label(reader)
        def block(env):
            target = env.label[label]
            if not isinstance(target, Number):
                raise SemanticError("Label is not a numerical value")
            return target
        return block
    return None

def _negate_expr(reader):
    if reader.go("@{["):
        expr = read_expr(reader)
        reader.must("]}")
        return lambda env: - expr(env)
    return None

def read_expr(reader):
    def expressions():
        yield _cycle_expr(reader)
        yield _zero_expr(reader)
        yield _incr_expr(reader)
        yield _label_expr(reader)
        yield _negate_expr(reader)
    for e in expressions():
        if e: return e
    raise ParseError("Expression expected")

def _bind_statement(reader):
    if not reader.go("synchronized("):
        return None
    line = reader.line
    label = read_label(reader)
    reader.must("){")
    stmts = read_statements(reader)
    reader.must("}")
    def block(env):
        with env.label.bind(label, line):
            for stmt in stmts:
                stmt(env)
    return block

def _load_statement(reader):
    if not reader.go("std::cout<<"):
        return None
    expr = read_expr(reader)
    reader.must("<<std::endl;")
    def block(env):
        env.var_a = expr(env)
    return block

def _cycle_statement(reader):
    if not reader.go("goto"):
        return None
    label = read_label(reader)
    reader.must(";")
    def block(env):
        target = env.label[label]
        if not isinstance(target, Number):
            raise SemanticError("Label is not a numerical value")
        if target % 2 == 0:
            env.var_a, env.var_c, env.var_e = env.var_e, env.var_a, env.var_c
        else:
            env.var_a, env.var_c, env.var_e = env.var_c, env.var_e, env.var_a
    return block

def _loop_statement(reader):
    if not reader.go("(format"):
        return None
    label = read_label(reader)
    reader.must('"')
    stmts = read_statements(reader)
    reader.must('")')
    def block(env):
        bstmt = BCStatement()
        cstmt = BCStatement()
        def trigger(x):
            if x is trigger_a:
                raise bstmt
            elif x is trigger_b:
                raise cstmt
            else:
                raise SemanticError("Invalid trigger passed")
        with env.label.bind(label, trigger):
            while env.var_c > 0:
                try:
                    for stmt in stmts:
                        stmt(env)
                except BCStatement as bc:
                    if bc is bstmt:
                        break
                    elif bc is cstmt:
                        pass # continue
                    else:
                        raise
                env.var_c -= 1
    return block

def _trigger_statement(reader):
    trigger = None
    label = None
    for t in [trigger_a, trigger_b]:
        before, after = t[reader.state[t]]
        if reader.go(before):
            reader.state[t] += 1
            trigger = t
            label = read_label(reader)
            reader.must(after)
            break
    if trigger is None:
        return None
    def block(env):
        target = env.label[label]
        if not callable(target):
            raise SemanticError("Label is not a code block")
        target(trigger)
    return block

def _print_statement(reader):
    if not reader.go("proc"):
        return None
    label = read_label(reader)
    reader.must("{")
    expr = read_expr(reader)
    reader.must("}{")
    stmts = read_statements(reader)
    reader.must("}")
    def block(env):
        def trigger(x):
            res = expr(env)
            if x is trigger_a:
                print(chr(res))
            elif x is trigger_b:
                print(res)
            else:
                raise SemanticError("Invalid trigger passed")
        with env.label.bind(label, trigger):
            for stmt in stmts:
                stmt(env)
    return block

def _store_statement(reader):
    if not reader.go("WHILE"):
        return None
    label = read_label(reader)
    op = read_op(reader)
    expr = read_expr(reader)
    stmts = read_statements(reader)
    reader.must("WEND")
    def block(env):
        stored = env.var_e
        def trigger(x):
            nonlocal stored
            if x is trigger_a:
                if op == '<':
                    stored += env.var_e
                elif op == '>':
                    stored /= env.var_e
                elif op == '=':
                    stored -= 1
                else:
                    raise SemanticError("Invalid operation")
            elif x is trigger_b:
                if op == '<':
                    stored -= env.var_e
                elif op == '>':
                    stored *= env.var_e
                elif op == '=':
                    stored += 1
                else:
                    raise SemanticError("Invalid operation")
            else:
                raise SemanticError("Invalid trigger passed")
        try:
            env.var_e = expr(env)
            with env.label.bind(label, trigger):
                for stmt in stmts:
                    stmt(env)
        finally:
            env.var_e = stored
    return block

def _input_statement(reader):
    if not reader.go("case"):
        return None
    label = read_label(reader)
    reader.must("of{_->")
    stmts = read_statements(reader)
    reader.must("}")
    def block(env):
        def trigger(x):
            if x is trigger_a:
                env.var_a = int(input())
            elif x is trigger_b:
                env.var_a = ord(sys.stdin.read(1))
            else:
                raise SemanticError("Invalid trigger passed")
        with env.label.bind(label, trigger):
            for stmt in stmts:
                stmt(env)
    return block

def _stack_statement(reader):
    if not reader.go("def"):
        return None
    label = read_label(reader)
    reader.must("(")
    expr = read_expr(reader)
    reader.must(")")
    stmts = read_statements(reader)
    reader.must("end")
    def block(env):
        def trigger(x):
            if x is trigger_a:
                env.stack[expr(env) % 3].append(env.var_a)
            elif x is trigger_b:
                e = expr(env)
                if env.stack[e]:
                    env.var_a = env.stack[e][-1]
                    env.stack[e] = env.stack[e][:-1]
                else:
                    env.var_a = 0
            else:
                raise SemanticError("Invalid trigger passed")
        with env.label.bind(label, trigger):
            for stmt in stmts:
                stmt(env)
    return block

def read_statement_maybe(reader):
    def statements():
        yield _bind_statement(reader)
        yield _load_statement(reader)
        yield _cycle_statement(reader)
        yield _loop_statement(reader)
        yield _trigger_statement(reader)
        yield _print_statement(reader)
        yield _store_statement(reader)
        yield _input_statement(reader)
        yield _stack_statement(reader)
    for s in statements():
        if s: return s
    return None

def read_statement(reader):
    res = read_statement_maybe(reader)
    if res:
        return res
    else:
        raise ParseError("Statement expected")

def read_statements(reader):
    arr = []
    x = read_statement_maybe(reader)
    while x:
        arr.append(x)
        x = read_statement_maybe(reader)
    return arr

with open(sys.argv[1]) as fh:
    reader = Reader(fh.read())
    env = Environment()
    read_statement(reader)(env)
