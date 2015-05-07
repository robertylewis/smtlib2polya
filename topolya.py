from parser2.smtparser import SMTParser as p
import polya
import polya.main.terms as terms
import polya.main.formulas as formulas
import fractions
import copy
import numbers


def translate_smt_node(cmds, force_fm=False, force_smt=False):
    """
    Returns 1 if the list of commands asks to check-sat an unsatisfiable problem. Returns -1 if
    Polya has tried and failed to determine unsatisfiability. Returns 0 if check-sat is never asked.
    """
    if force_fm:
        polya.set_solver_type('fm')
    else:
        polya.set_solver_type('poly')
    #e = polya.Example(conc=None)  # split_depth=2
    exlist = [polya.Example(conc=None)]
    #exs = [polya.Example(conc=None)]

    funs = {}
    vars = {}
    status = [0]

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
            return smt_to_polya_comps[fmla.kind](
                translate_term(fmla.children[0]), translate_term(fmla.children[1])
            )
        else:
            raise Exception()

    def translate_formula(fmla):
        if fmla.kind == 'not':
            return polya.Not(translate_formula(fmla.children[0]))
        elif fmla.kind == 'and':
            return polya.And(*[translate_formula(c) for c in fmla.children])
        elif fmla.kind == 'or':
            return polya.Or(*[translate_formula(c) for c in fmla.children])
        elif fmla.kind == '=>':
            return polya.Implies(
                translate_formula(fmla.children[0]), translate_formula(fmla.children[1])
            )
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
            return formulas.Exist(set(vars1), translate_formula(fmla.children[0]))
        elif fmla.kind == 'forall':
            vars1 = []
            for c in fmla.svars:
                if str(c.sort) != 'Real':
                    raise Exception('Quantifying over non-real variables')
                vars1.append(polya.Var(str(c)))
            return formulas.Univ(set(vars1), translate_formula(fmla.children[0]))
        elif fmla.kind == '<const bool>':
            if fmla.value == 'true':
                return terms.one == terms.one
            elif fmla.value == 'false':
                return terms.one != terms.one
            else:
                raise Exception('dont understand boolean type')
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

    def def_fun(l):
        #todo : finish this
        name, input, output = '', '', ''
        #print 'def_fun:', name, input, output
        add_fun(l)
        e.add_axiom()  # figure this part out

    def set_comment(c):
        #print 'set_comment:', c
        for e in exlist:
            e.comment = (e.comment + c if e.comment else c)

    def make_assertion(a):
        #print 'make_assertion:', str(a[0])
        #print a[0]
        fmla = formulas.pnf(translate_formula(a[0]))
        make_translated_assertion(fmla)

    def var_occurs_in_clause(var, list):
        """
        Checks whether var occurs in some term comparison in list.
        """
        for tc in list:
            tc2 = tc.substitute({var.key: terms.Var(var.name + '1')})
            if str(tc2) != str(tc):
                return True
        return False

    def make_translated_assertion(fmla):
        if isinstance(fmla, formulas.Exist):
            vars1 = fmla.vars
            for v in vars1:
                if v in vars:
                    nv = polya.Var(v.name+".1")
                    s = vars1.difference({v}).union({nv})
                    return make_assertion(
                        formulas.Exist(s, fmla.substitute({v.key: nv}))
                    )
            for v in vars1:
                vars[v.name] = v
                return make_translated_assertion(fmla.formula)

        elif isinstance(fmla, formulas.Univ):
            if isinstance(fmla.formula, formulas.Exist):
                raise Exception('Cannot interpret universal over existential')
            elif isinstance(fmla.formula, formulas.Univ):
                return make_translated_assertion(formulas.Univ(
                    fmla.vars.union(fmla.formula.vars), fmla.formula.formula)
                )
            else:
                clauses = formulas.cnf(fmla.formula)
                ovars = [[v for v in fmla.vars if var_occurs_in_clause(v, cls)] for cls in clauses]
                for (i, cls) in enumerate(clauses):
                    if len(ovars[i]) > 0:
                        try:
                            fmla1 = formulas.Or(*cls)
                            univ = polya.Forall(ovars[i], fmla1)
                            a = formulas.Axiom(*univ.to_cnf())
                            for e in exlist:
                                e.axioms.append(univ)
                        except formulas.AxiomException:
                            print 'Warning: axiom in the wrong form. {0}'.format(str(fmla))
                    else:
                        for e in exlist:
                            e.clauses.append(cls)

        else:
            conjuncts = formulas.dnf(fmla) # or of ands
            nexmps = []
            for e in exlist:
                for l in conjuncts:
                    e2 = copy.deepcopy(e)
                    for c in l:
                        e2.hyps.append(c)
                    nexmps.append(e2)
            while len(exlist) > 0:
                exlist.pop(0)
            exlist.extend(nexmps)
            # clauses = formulas.cnf(fmla)
            # if any(len(l) != 1 for l in clauses):
            #     print clauses
            #     raise Exception('Wrong logical structure for Polya')
            #
            # for l in clauses:
            #     e.hyps.append(l[0])
        #print clauses

    def polya_to_smt(pterm):
        """
        Translates a Polya term to an SMT term
        """
        if isinstance(pterm, int):
            return str(pterm)
        elif isinstance(pterm, float):
            return polya_to_smt(fractions.Fraction(pterm))
        elif isinstance(pterm, fractions.Fraction):
            if pterm.denominator == 1:
                return pterm.numerator
            else:
                return "(/ {0} {1})".format(pterm.numerator, pterm.denominator)
        elif isinstance(pterm, polya.main.terms.STerm):
            return polya_to_smt(pterm.term) if pterm.coeff == 1 else "(* {0} {1})".format(
                polya_to_smt(pterm.coeff), polya_to_smt(pterm.term)
            )
        elif isinstance(pterm, polya.main.terms.Var):
            return str(pterm.name)
        elif isinstance(pterm, polya.main.terms.AddTerm):
            if len(pterm.args) == 0:
                return 'ADD_ERROR'
            elif len(pterm.args) == 1:
                return polya_to_smt(pterm.args[0])
            else:
                return "(+ {0} {1})".format(polya_to_smt(pterm.args[0]),
                                            polya_to_smt(polya.main.terms.AddTerm(pterm.args[1:])))
        elif isinstance(pterm, polya.main.terms.MulPair):
            if pterm.exponent == 1:
                return polya_to_smt(pterm.term)
            elif pterm.exponent > 0:
                return "(* {0} {1})".format(polya_to_smt(pterm.term),
                                            polya_to_smt(pterm.term**(pterm.exponent - 1)))
            elif pterm.exponent < 0:
                return "(/ 1 {0})".format(polya_to_smt(pterm.term**(-pterm.exponent)))
        elif isinstance(pterm, polya.main.terms.MulTerm):
            if len(pterm.args) == 0:
                return 'MUL_ERROR'
            elif len(pterm.args) == 1:
                return polya_to_smt(pterm.args[0])
            else:
                return "(* {0} {1})".format(polya_to_smt(pterm.args[0]),
                                            polya_to_smt(polya.main.terms.MulTerm(pterm.args[1:])))
        elif isinstance(pterm, polya.main.terms.FuncTerm):
            return "({0} {1})".format(pterm.func.name, " ".join(polya_to_smt(a) for a in pterm.args))
        elif isinstance(pterm, polya.main.terms.One):
            return '1'

    def check_sat(a):
        polya.set_verbosity(polya.quiet)
        print '-----'
        print 'Checking sat. disjuncts: ', len(exlist)
        status[0] = 1 if all(e.test() for e in exlist) else -1
        print 'RESULT: 1 (UNSAT)' if status[0] == 1 else 'RESULT: -1 (POSSIBLY SAT)'
        print '-----'

    def simplify(a):
        print '-----'
        print 'Simplifying term:', a
        if not force_smt:
            status[0] = translate_term(a[0]).canonize()
        else:
            status[0] = polya_to_smt(translate_term(a[0]).canonize())
        print status[0]
        print '-----'

    map = {
        p.SETLOGIC: lambda x: None,
        p.SETOPT: lambda x: None,
        p.SETINFO: set_comment,
        p.DECLSORT: lambda x: None,  # do this one
        p.DECLFUN: lambda smtfunnode: add_fun(smtfunnode[0]),
        p.DEFFUN: lambda list: def_fun(list),
        p.POP: lambda x: None,
        p.PUSH: lambda x: None,
        p.ASSERT: make_assertion,
        p.CHECKSAT: check_sat,
        p.GETASSERT: lambda x: None,
        p.GETPROOF: lambda x: None,
        p.GETUCORE: lambda x: None,
        p.GETVALUE: lambda x: None,
        p.GETASSIGN: lambda x: None,
        p.GETOPT: lambda x: None,
        p.GETINFO: lambda x: None,
        p.EXIT: lambda x: None,
        p.SIMPLIFY: lambda x: simplify(x)

    }

    for c in cmds:
        map[c.kind](c.children)
    return status[0]