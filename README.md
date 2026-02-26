from dataclasses import dataclass

Precedence = {
    '!':4,
    '&':3,
    '^': 2,
    '|':1,
}

Assoc = {
    '!': 'right',
    '&': 'left',
    '^':'left',
    '|': 'left',
}

def label(expr: str) -> list[tuple[str, str]]:
    labels = [] 
    i = 0 
    while i < len(expr): 
        character = expr[i] 
        if character.isspace(): 
            i += 1 
            continue 

        if character in ['!', '&', '^', '|', '(', ')', ',']:
            labelType = {
                '!' : 'OP',
                '&' : 'OP',
                '^' : 'OP',
                '|' : 'OP',
                '(' : 'LPAREN',
                ')' : 'RPAREN',
                ',' : 'COMMA',
            }[character] 
            labels.append((labelType, character)) 
            i += 1 
            continue
        if character in ['0', '1']:
            labels.append(('CONST', character)) 
            i += 1 
            continue 
        if character.isalpha() or character == '_':
            j = i
            while j < len(expr) and (expr[j].isalnum() or expr[j] == '_'):
                j += 1
            ident = expr[i:j]
            if ident == 'nor':
                labels.append(('FUNC', ident))
            else:
                labels.append(('IDENT', ident))
            i = j
            continue

        raise ValueError(f"Unexpected character: {character}")
    return labels
    
def reorderForEval(labels: list[tuple[str, str]]) -> list[tuple[str, str]]:
    output = []
    stack = [] 

    for labelType, val in labels: 
        if labelType in ('CONST', 'IDENT'): 
            output.append((labelType, val)) 

        elif labelType == 'FUNC': 
            stack.append((labelType, val))

        elif labelType == 'COMMA': 
            while stack and stack [-1][0] != 'LPAREN': 
                output.append(stack.pop())

        elif labelType == 'OP':
            while(
                stack 
                and stack[-1][0] == 'OP'
                and ( 
                    (Assoc[val]== 'left' and Precedence[val] <= Precedence[stack[-1][1]])
                    or (Assoc[val] == 'right' and Precedence[val] < Precedence[stack[-1][1]])
                )   
            ):
                output.append(stack.pop())
            stack.append((labelType, val))

        elif labelType == 'LPAREN':
            stack.append((labelType, val))

        elif labelType == 'RPAREN': 
            while stack and stack[-1][0] != 'LPAREN': 
                output.append(stack.pop())
            if not stack: 
                raise ValueError("Mismatched parentheses.")
            stack.pop()
            if stack and stack[-1][0] == 'FUNC':
                output.append(stack.pop())
    while stack: 
        output.append(stack.pop())

    return output




def evalReorder(reorder: list[tuple[str, str]], env: dict[str, int]) -> int:
    stack = [] 

    for labelType, val in reorder: 
        if labelType == 'CONST':
            stack.append(int(val)) 

        elif labelType == 'IDENT':
            stack.append(int(env[val]))

        elif labelType == 'OP':
            if val == '!':
                a = stack.pop() 
                stack.append(0 if a else 1) 
            else: 
               b = stack.pop()
               a = stack.pop()
               if val == '&':
                   stack.append(int(a and b)) 
               elif val == '^': 
                   stack.append(a ^ b) 
               elif val == '|': 
                   stack.append(int(a or b)) 
        elif labelType == 'FUNC':
            y = stack.pop()
            x = stack.pop() 
            stack.append(0 if (x or y) else 1)    
    return stack[0]       


def expressionEval(expr: str, env: dict[str, int]) -> int: 
    return evalReorder(reorderForEval(label(expr)), env)


@dataclass 
class Gate: 
    dest: str
    op: str | None 
    args: list[str] 

def parseCircuit(netlist: str) -> list[Gate]:
    gates = []

    for line in netlist.strip().splitlines(): 
        dest, rhs = [p.strip() for p in line.split('=')]

        if '(' not in rhs: 
            gates.append(Gate(dest, None, [rhs]))
        else: 
            op = rhs.split('(')[0].strip()
            inside = rhs.split('(')[1].split(')')[0]
            args = [a.strip() for a in inside.split(',')]
            gates.append(Gate(dest, op.upper(), args))

    return gates


def gateEval(op: str, args: list[int]) -> int: 
    if op == 'NOT': 
        return 0 if args[0] else 1
    if op == 'AND':
        return int(args[0] and args[1])
    if op == 'OR':
        return int(args[0] or args[1])
    if op == 'XOR': 
        return args[0] ^ args[1] 
    if op == 'NOR': 
        return 0 if (args[0] or args[1]) else 1 
    raise ValueError("Unknown gate") 


def circuitEval(gates: list[Gate], env: dict[str, int]) -> int: 
    wires = dict(env) 

    for g in gates: 
        if g.op is None: 
            wires[g.dest] = wires[g.args[0]]
        else: 
            vals = [wires[a] for a in g.args]
            wires[g.dest] = gateEval(g.op, vals)

    return wires['OUT']

def truthTable(expr: str, varsOrder: list[str]) -> list[int]: 
    outputs = [] 
    if len(varsOrder) == 2: 
        for A in [0,1]: 
            for B in [0,1]:
                outputs.append(expressionEval(expr, {'A': A, 'B': B}))
    else: 
        for A in [0,1]: 
            for B in [0,1]: 
                for C in [0,1]: 
                    outputs.append(expressionEval(expr, {'A': A, 'B': B,'C': C }))
    return outputs  


def truthTableCircuit(gates: list[Gate]) -> list [int]:
    outputs = [] 
    for A in [0,1]: 
        for B in [0,1]:
            for C in [0,1]:
                outputs.append(circuitEval(gates, {'A': A, 'B': B,'C': C}))
    return outputs


def truthTablesPrint(varsOrder: list[str], outputs: list[int]) -> None: 
    print (" ".join(varsOrder) + "| F")
    print("-" * (len(varsOrder)* 2 + 3))

    idx = 0 
    if len(varsOrder) == 2: 
        for A in [0,1]: 
            for B in [0,1]: 
                print(f"{A} {B} | {outputs[idx]}")
                idx +=1
    else:
        for A in [0,1]: 
            for B in [0,1]:
                for C in [0,1]:
                    print(f"{A} {B} {C} | {outputs[idx]}" )
                    idx += 1



def minterms(outputs: list[int]) -> list[int]: 
    return [i for i, v in enumerate(outputs) if v == 1]
         


def runExpression(label, expr, assignment, varsOrder): 
    print("=" * 60)
    print(label)
    print("Expression:" , expr)
    print("evaluate with:" , assignment) 
    result = expressionEval(expr, assignment)
    print("Result:", result)

    outs = truthTable(expr, varsOrder)
    print("\nTruth Table:")
    truthTablesPrint(varsOrder, outs)

    print("\nMinterms:Σm(" + ", ".join(map(str, minterms(outs))) + ")")
    return outs

def runCircuit(netlist):
    print("="*60)
    print("Circuit Demo")
    print(netlist)

    gates = parseCircuit(netlist)
    result = circuitEval(gates, {'A': 1, 'B': 0, 'C':1})
    print("Evaluate with: A =1, B=0, C=1")
    print("Result:", result)

    outs = truthTableCircuit(gates)
    print("\nTruth Table:") 
    truthTablesPrint(['A', 'B','C'], outs)

    print("\nMinterms: Σm(" + ", ".join(map(str, minterms(outs))) + ")")
    return outs







def main(): 
    expr2A = "!(A & B)"
    expr2B = "!(A | (A ^ B))"
    expr3A = "!(A | (B ^ C))"
    expr3B = "(!A & (B | C)) | (A & !(B | C))"

    circuit = """ 
g1 = XOR(B,C)
g2 = NOR(A, g1) 
OUT = g2 
"""

    runExpression("Expr 2A", expr2A, {'A': 1, 'B': 1}, ['A', 'B'])
    runExpression("Expr 2B", expr2B, {'A': 1, 'B': 0}, ['A', 'B'])
    outExpr3A = runExpression("Expr 3A",expr3A,{'A': 1, 'B': 0, 'C': 1}, ['A', 'B', 'C'] )
    runExpression("Expr 3B", expr3B, {'A': 0, 'B': 1, 'C': 0}, ['A','B','C'])

    outsCircuit = runCircuit(circuit)

    print("=" * 60) 
    print("Equivalence Check (Expr 3A vs Circuit):")
    if outExpr3A == outsCircuit: 
        print("Equivalent.")
    else: 
        print("Not equivalent.")
    print("="*60)

if __name__ == "__main__":
    main()

