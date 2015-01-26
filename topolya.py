    # SETLOGIC  = "set-logic"
    # SETOPT    = "set-option"
    # SETINFO   = "set-info"
    # DECLSORT  = "declare-sort"
    # DEFSORT   = "define-sort"
    # DECLFUN   = "declare-fun"
    # DEFFUN    = "define-fun"
    # PUSH      = "push"
    # POP       = "pop"
    # ASSERT    = "assert"
    # CHECKSAT  = "check-sat"
    # GETASSERT = "get-assertions"
    # GETPROOF  = "get-proof"
    # GETUCORE  = "get-unsat-core"
    # GETVALUE  = "get-value"
    # GETASSIGN = "get-assignment"
    # GETOPT    = "get-option"
    # GETINFO   = "get-info"
    # EXIT      = "exit"

from parser.smtparser import SMTParser as p
import polya
import fractions



def translate_smt_node(cmds):
    e = polya.Example(conc=None)
    funs = {}
    vars = {}

    smt_to_polya_comps = {
        "<=": lambda x, y: x <= y,
        "<": lambda x, y: x < y,
        ">=": lambda x, y: x >= y,
        ">": lambda x, y: x > y,
        "=": lambda x, y: x == y
    }
    smt_to_polya_ops = {
        "distinct": lambda l: l[0] != l[1],

        "abs": lambda l: abs(l[0]),
        "+": lambda l: reduce(lambda x, y: x + y, l),
        "div": lambda l: l[0]/l[1],
        "/": lambda l: l[0]/l[1],
        "*": lambda l: reduce(lambda x, y: x*y, l),
        "neg": lambda l: -l[0],
        "-": lambda l: l[0] - l[1]
    }

    def translate_term(term):
        if term.kind in smt_to_polya_ops:
            return smt_to_polya_ops[term.kind]([translate_term(c) for c in term.children])
        elif term.kind == '<const dec>' or term.kind == '<const num>':
            if str(int(float(str(term)))) == str(float(str(term))):
                return int(float(str(term)))
            else:
                return fractions.Fraction(str(term))
        elif term.kind == '<var or fun symbol>':
            if term.name in funs:
                return funs[term.name](*[translate_term(c) for c in term.children])
            elif term.name in vars:
                return vars[term.name]
            else:
                raise Exception()
        else:
            print 'didnt find kind:', term, term.kind
            return polya.Var('c')

    def translate_comparison(fmla):
        if fmla.kind in smt_to_polya_comps and len(fmla.children) == 2:
            return smt_to_polya_comps[fmla.kind](translate_term(fmla.children[0]),
                                            translate_term(fmla.children[1]))
        else:
            raise Exception()

    def translate_formula(fmla):
        if fmla.kind == 'not':
            return polya.Not(translate_formula(fmla.children[0]))
        elif fmla.kind == 'and':
            return polya.And(*[translate_formula(c) for c in fmla.children])
        elif fmla.kind == 'or':
            print 'or from', [str(c)+" of type " + c.kind for c in fmla.children]
            return polya.Or(*[translate_formula(c) for c in fmla.children])
        elif fmla.kind == '=>':
            return polya.Implies(translate_formula(fmla.children[0]), translate_formula(fmla.children[1]))
        elif fmla.kind == 'xor':
            a, b = translate_formula(fmla.children[0]), translate_formula(fmla.children[1])
            return polya.And(polya.Or(a, b), polya.Or(polya.Not(a), polya.Not(b)))
        elif fmla.kind == 'ite':
            raise Exception('dont understand boolean ite')
        elif fmla.kind == 'exists':
            vars1 = []
            for c in fmla.svars:
                if str(c.sort) != 'Real':
                    raise Exception('Quantifying over non-real variables')
                vars1.append(polya.Var(str(c)))
            return polya.main.formulas.Exist(set(vars1), translate_formula(fmla.children[0]))
        elif fmla.kind == 'forall':
            vars1 = []
            for c in fmla.svars:
                if str(c.sort) != 'Real':
                    raise Exception('Quantifying over non-real variables')
                vars1.append(polya.Var(str(c)))
            return polya.main.formulas.Univ(set(vars1), translate_formula(fmla.children[0]))
        elif fmla.kind in smt_to_polya_comps:
            return translate_comparison(fmla)
        else:
            raise Exception('dont understand type:'+fmla.kind)

    def add_fun(smtfunnode):
        #print 'add_fun:', smtfunnode.name, smtfunnode.sorts, smtfunnode.sort
        if str(smtfunnode.sort) != 'Real':
            print 'Error: wrong sort'
            quit()
        arity = len(smtfunnode.sorts)
        if arity > 0:
            if any(str(s) != 'Real' for s in smtfunnode.sorts):
                print 'Error: wrong sort'
                quit()
            funs[smtfunnode.name] = polya.Func(smtfunnode.name, arity)
        else:
            vars[smtfunnode.name] = polya.Var(smtfunnode.name)

    def def_fun(list):
        name, input, output = '', '', ''
        #print 'def_fun:', name, input, output
        add_fun(list)
        e.add_axiom() #figure this part out

    def set_comment(c):
        #print 'set_comment:', c
        e.comment = (e.comment + c if e.comment else c)

    def make_assertion(a):
        #print 'make_assertion:', a
        #print a[0]
        fmla = polya.main.formulas.pnf(translate_formula(a[0]))
        make_translated_assertion(fmla)

    def make_translated_assertion(fmla):

        if isinstance(fmla, polya.main.formulas.Exist):
            vars1 = fmla.vars
            for v in vars1:
                if v in vars:
                    nv = polya.Var(v.name+".1")
                    s = vars1.difference({v}).union({nv})
                    return make_assertion(
                        polya.main.formulas.Exist(s, fmla.substitute({v.key: nv}))
                    )
            for v in vars1:
                vars[v.name] = v
                return make_translated_assertion(fmla.formula)

        elif isinstance(fmla, polya.main.formulas.Univ):
            if isinstance(fmla.formula, polya.main.formulas.Exist):
                raise Exception('Cannot interpret universal over existential')
            elif isinstance(fmla.formula, polya.main.formulas.Univ):
                return make_translated_assertion(polya.main.formulas.Univ(
                    fmla.vars.union(fmla.formula.vars), fmla.formula.formula)
                )
            else:
                e.axioms.append(polya.Forall(list(fmla.vars), fmla.formula))

        else:
            clauses = polya.main.formulas.cnf(fmla)

            # TODO: DNF translation, right now assume this is all ands
            if any(len(l) != 1 for l in clauses):
                print clauses
                raise Exception('Wrong logical structure for Polya')

            for l in clauses:
                e.hyps.append(l[0])

        #print clauses

    def check_sat(a):
        polya.set_verbosity(polya.quiet)
        e.test()

    map = {
        p.SETLOGIC: lambda x:None,
        p.SETOPT: lambda x:None,
        p.SETINFO: set_comment,
        p.DECLSORT: lambda x:None, # do this one
        p.DECLFUN: lambda smtfunnode:add_fun(smtfunnode[0]),
        p.DEFFUN: lambda list:def_fun(list),
        p.POP: lambda x:None,
        p.PUSH: lambda x:None,
        p.ASSERT: make_assertion,
        p.CHECKSAT: check_sat,
        p.GETASSERT: lambda x:None,
        p.GETPROOF: lambda x:None,
        p.GETUCORE: lambda x:None,
        p.GETVALUE: lambda x:None,
        p.GETASSIGN: lambda x:None,
        p.GETOPT: lambda x:None,
        p.GETINFO: lambda x:None,
        p.EXIT: lambda x:quit()


        }

    for c in cmds:
        map[c.kind](c.children)