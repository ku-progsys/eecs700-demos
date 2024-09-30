import ast

FILENAME = "sample.py"
with open(FILENAME, 'r') as f:
    src = ast.parse(f.read())

def interp(env, prog):
    if type(prog) is ast.Module:
        stmts = prog.body
        for stmt in stmts:
            [env, ret] = interp(env, stmt)
        return [env, ret]
    elif type(prog) is ast.Assign:
        id = prog.targets[0].id
        [env, val] = interp(env, prog.value)
        env[id] = val
        return [env, val]

    elif type(prog) is ast.Constant:
        return [env, prog.value]

    elif type(prog) is ast.If:
        [env, ret] = interp(env, prog.test)
        if not ret:
            for stmt in prog.orelse:
                [env, ret] = interp(env, stmt)
            return [env, ret]
        else:
            for stmt in prog.body:
                [env, ret] = interp(env, stmt)
            return [env, ret]

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
            return [env, left and right]
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
        if not val:
            raise RuntimeError("Assertion does not hold!")
        return [env, 1]
    else:
        raise RuntimeError("Unhandled AST node: {}".format(prog))

print(interp({}, src))

