import ast
import z3
from copy import deepcopy

FILENAME = "sample_sym.py"
with open(FILENAME, 'r') as f:
    src = ast.parse(f.read())

assigning_rn = None

def merge_val(val_1, val_2, test_expr):
    return z3.If(test_expr, val_1, val_2)

def merge_env(env_1, env_2, test_expr):
    env = {}
    for k in env_1.keys():
        env[k] = merge_val(env_1[k], env_2[k], test_expr)
    return env

def interp(env, prog):
    if type(prog) is ast.Module:
        stmts = prog.body
        for stmt in stmts:
            [env, ret] = interp(env, stmt)
        return [env, ret]
    elif type(prog) is ast.Assign:
        id = prog.targets[0].id
        global assigning_rn
        assigning_rn = id
        [env, val] = interp(env, prog.value)
        env[id] = val
        assigning_rn = None
        return [env, val]
    elif type(prog) is ast.Constant:
        return [env, prog.value]
    elif type(prog) is ast.If:
        [env, test_expr] = interp(env, prog.test)
        env_1 = deepcopy(env)
        env_2 = deepcopy(env)

        for stmt in prog.orelse:
            [env_1, _] = interp(env_1, stmt)

        for stmt in prog.body:
            [env_2, _] = interp(env_2, stmt)
        env = merge_env(env_1, env_2, test_expr)
        return [env, 0]

    elif type(prog) is ast.Name:
        return [env, env[prog.id]]
    elif type(prog) is ast.Compare:
        [env, left] = interp(env, prog.left)
        [env, right] = interp(env, prog.comparators[0])
        if type(prog.ops[0]) is ast.Lt:
            return [env, left < right]
        elif type(prog.ops[0]) is ast.Gt:
            return [env, left > right]
        elif type(prog.ops[0]) is ast.Eq:
            return [env, left == right]
        elif type(prog.ops[0]) is ast.NotEq:
            return [env, left != right]
        else:
            raise RuntimeError("Unsupported comparison: {}".format(prog.ops[0]))
    elif type(prog) is ast.BoolOp:
        [env, left] = interp(env, prog.values[0])
        [env, right] = interp(env, prog.values[1])
        if type(prog.op) is ast.And:
            return [env, z3.If(left & right, True, False)]
        else:
            raise RuntimeError("Unsupported boolop: {}".format(prog.op))
    elif type(prog) is ast.UnaryOp:
        [env, val] = interp(env, prog.operand)
        if type(prog.op) is ast.USub:
            return [env, -val]
        else:
            raise RuntimeError("Unsupported unop: {}".format(prog.op))
    elif type(prog) is ast.BinOp:
        [env, left] = interp(env, prog.left)
        [env, right] = interp(env, prog.right)
        if type(prog.op) is ast.Add:
            return [env, left + right]
        else:
            raise RuntimeError("Unsupported binop: {}".format(prog.op))
    elif type(prog) is ast.Assert:
        [env, val] = interp(env, prog.test)
        # print(val)
        s = z3.Solver()
        s.add(val)
        if s.check() == z3.sat:
            raise RuntimeError("Counterexample found: {}".format(s.model()))
        else:
            return [env, 1]
    elif type(prog) is ast.Call:
        if prog.func.id == "sym" and len(prog.args) == 0:
            return [env, z3.Int(assigning_rn)]
        else:
            raise RuntimeError("Unexpected function call")
    else:
        raise RuntimeError("Unhandled AST node: {}".format(prog))

print(interp({}, src))
