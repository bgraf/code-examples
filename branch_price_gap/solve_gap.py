from typing import List, Dict
from dataclasses import dataclass, field
from pyscipopt import Model, Pricer, Variable, Constraint, SCIP_RESULT, SCIP_PARAMSETTING, Branchrule, Eventhdlr, SCIP_EVENTTYPE, SCIP_STATUS, SCIP_LPSOLSTAT
import math
from argparse import ArgumentParser


@dataclass
class GAP:
    c: List[List[int]]
    l: List[List[int]]
    w: List[int]
    n: List[int]

    def jobs(self):
        return range(len(self.c[0]))

    def machines(self):
        return range(len(self.c))

class Infeasible(Exception):
    """ Raised by solvers on infeasible problems """
    pass


@dataclass
class PricingResult:
    js: List[int]
    cost: int


def solve_pricing(problem: GAP, k: int, duals: List[float], k_dual: float) -> PricingResult:
    model = Model()
    model.hideOutput()

    print("k=", k)
    print("j_duals=", duals)
    print("k_duals=", k_dual)

    x = [
        model.addVar(vtype='I', lb=0, ub=1, name=f'j_{j}')
        for j in problem.jobs()
    ]

    model.addCons(
        sum(x[j] * problem.l[k][j] for j in problem.jobs()) <= problem.w[k]
    )

    model.setObjective(sum(
        x[j] * (duals[j] - problem.c[k][j])
        for j in problem.jobs()
    ))

    model.setMaximize()
    model.optimize()

    c = -model.getObjVal() - k_dual

    print("obj=", c)

    if c >= -0.0001:
        return None

    sol = model.getBestSol()
    js = [
        1 if model.getSolVal(sol, x[j]) > 0.5 else 0
        for j in problem.jobs()
    ]
    print("js=", js)

    cost = sum(problem.c[k][j] for j in problem.jobs() if js[j] >= 1)

    model.freeTransform()
    model.freeProb()

    return PricingResult(js=js, cost=cost)


@dataclass
class Column:
    js: List[int]
    machine: int
    cost: int
    var: Variable


@dataclass
class BranchingDecision:
    j: int
    k: int
    cons: Constraint
    down: bool


@dataclass
class State:
    problem: GAP
    columns: List[Column]
    j_constraints: List[Constraint]
    k_constraints: List[Constraint]
    branches: Dict[int, List[BranchingDecision]] = field(default_factory=dict)

    def original_solution(self, model: Model) -> (List[List[float]], bool):
        original = [
            [0 for _ in self.problem.jobs()]
            for _ in self.problem.machines()
        ]

        contains_artificial = False

        for col in self.columns:
            if col.machine is None:
                continue

            solval = model.getSolVal(None, col.var)
            if solval > 0.001:
                if col.machine is None:
                    contains_artificial = True
            for j, incidence in zip(self.problem.jobs(), col.js):
                original[col.machine][j] += incidence * solval
        return original, contains_artificial


@dataclass
class GapPricer(Pricer):
    s: State

    def pricerredcost(self):
        return self.price()

    def pricerfarkas(self):
        print("FARKAS")
        print("  node =     ", self.model.getCurrentNode().getNumber())
        print("  LP status =", self.model.getLPSolstat(),
              "<=>", SCIP_LPSOLSTAT.INFEASIBLE, "(infeasible)")

        node_id = self.model.getCurrentNode().getNumber()
        for bd in self.s.branches.get(node_id, []):
            print(bd)
        raise RuntimeError("Farkas pricing called")

    def price(self):
        print("=== Pricing ===")

        def dual(cons: Constraint) -> float:
            return self.model.getDualsolLinear(self.model.getTransformedCons(cons))

        j_duals = [dual(c) for c in self.s.j_constraints]
        k_duals = [dual(c) for c in self.s.k_constraints]
        print("j_duals (orig) =", j_duals)

        j_duals_by_k = [
            list(j_duals)
            for _ in self.s.problem.machines()
        ]

        node_id = self.model.getCurrentNode().getNumber()
        for bd in self.s.branches.get(node_id, []):
            d = dual(bd.cons)
            print(
                f"brach dual={d} (c_jk = {self.s.problem.c[bd.k][bd.j]}), k={bd.k}, j={bd.j}, node={node_id}")
            j_duals_by_k[bd.k][bd.j] += d

        new_col_found = False

        for k in self.s.problem.machines():
            pr = solve_pricing(self.s.problem, k, j_duals_by_k[k], k_duals[k])
            if pr is None:
                continue

            new_col_found = True
            name = f'pat_{k}_' + ''.join(str(x) for x in pr.js)
            print("generated", name)
            var = self.model.addVar(
                vtype='I', ub=1, lb=0, pricedVar=True, obj=pr.cost, name=name,)

            column = Column(pr.js, k, pr.cost, var)
            self.s.columns.append(column)

            # Add to job-constraints
            for (j, c, coef) in zip(self.s.problem.jobs(), self.s.j_constraints, pr.js):
                if coef > 0:
                    self.model.addConsCoeff(
                        self.model.getTransformedCons(c), var, 1)

            # Add to machine constraints
            self.model.addConsCoeff(
                self.model.getTransformedCons(self.s.k_constraints[k]),
                var,
                1
            )

            # Add to branching constraints
            for bd in self.s.branches.get(node_id, []):
                if bd.down:
                    continue
                if bd.k == k and column.js[bd.j] > 0:
                    # Job contained in column and correct machine
                    self.model.addConsCoeff(
                        self.model.getTransformedCons(bd.cons), column.var, 1)

        return {'result': SCIP_RESULT.SUCCESS if new_col_found else SCIP_RESULT.DIDNOTFIND}


@dataclass
class GapBranching(Branchrule):
    s: State

    def branchexeclp(self, allowaddcons):
        print("=== Branching ===")
        node_id = self.model.getCurrentNode().getNumber()

        def make_branching_decisions(bd: BranchingDecision):
            parent_decisions = list(self.s.branches.get(node_id, []))
            parent_decisions.append(bd)
            return parent_decisions

        original, contains_artificial = self.s.original_solution(self.model)
        if contains_artificial:
            # If the current optimal LP solution contains one or more artificial variables
            # then the whole subtree is infeasible w.r.t. the original problem.
            return {"result": SCIP_RESULT.INFEASIBLE}

        for k in self.s.problem.machines():
            for j in self.s.problem.jobs():
                v = original[k][j]
                if abs(v - math.floor(v)) <= 0.01:
                    continue

                expr = sum(
                    col.var for col in self.s.columns if col.machine == k and col.js[j] > 0)
                artificial = sum(
                    col.var for col in self.s.columns if col.machine is None and col.js[j] > 0)

                # It's import to set `local=True`, otherwise SCIP will behave really strange and propagate
                # the constraint to other nodes outside the current subtree.
                child1 = self.model.createChild(1, 0)
                cons1 = self.model.createConsFromExpr(
                    expr <= math.floor(v), local=True, modifiable=True)
                self.model.addConsNode(child1, cons1)
                self.s.branches[child1.getNumber()] = make_branching_decisions(
                    BranchingDecision(j, k, cons1, down=True))

                # In the upper branch we allow artificial variables to ensure feasibility
                child2 = self.model.createChild(0, 0)
                cons2 = self.model.createConsFromExpr(
                    expr + artificial >= math.ceil(v), local=True, modifiable=True)
                self.model.addConsNode(child2, cons2)
                self.s.branches[child2.getNumber()] = make_branching_decisions(
                    BranchingDecision(j, k, cons2, down=False))

                return {"result": SCIP_RESULT.BRANCHED}

        return {"result": SCIP_RESULT.DIDNOTFIND}


def solve_branch_price(problem: GAP) -> List[int]:
    model = Model()

    model.setPresolve(SCIP_PARAMSETTING.OFF)
    model.setSeparating(SCIP_PARAMSETTING.OFF)
    model.setHeuristics(SCIP_PARAMSETTING.OFF)
    model.setParam("display/freq", 1)  # show the output log after each node

    columns: List[Column] = []
    for j in problem.jobs():
        js = [0 for _ in problem.jobs()]
        js[j] = 1
        var = model.addVar(vtype='C', ub=1, lb=0, name=f'DUMMY_{j}')
        columns.append(Column(
            cost=99,
            js=js,
            machine=None,
            var=var
        ))

    j_constraints: List[Constraint] = []
    for j in problem.jobs():
        j_constraints.append(model.addCons(
            sum(col.var * col.js[j] for col in columns) >= 1,
            name=f'c_job_{j}',
            modifiable=True,
        ))

    k_constraints: List[Constraint] = []
    for k in problem.machines():
        k_constraints.append(
            model.addCons(
                sum(0 * col.var for col in columns) <= problem.n[k],
                name=f'c_machine_{k}',
                modifiable=True
            )
        )

    model.setObjective(sum(col.cost * col.var for col in columns))

    state = State(problem, columns, j_constraints, k_constraints)

    model.includePricer(
        GapPricer(state),
        "GapPricer",
        "Pricer ...",
    )

    model.includeBranchrule(
        GapBranching(state),
        "GapBranching",
        "GAP branching rule",
        priority=100000,
        maxdepth=-1,
        maxbounddist=1.0
    )

    res = model.optimize()

    sol = model.getBestSol()

    assignment = [-1 for _ in problem.jobs()]
    cost = 0
    for col in columns:
        val = model.getSolVal(sol, col.var)
        if val > 0.5:
            if col.var.isOriginal():
                # Original dummy column in solution => infeasible!
                raise Infeasible()
            cost += col.cost
            for j, inc in zip(problem.jobs(), col.js):
                if inc >= 1:
                    assignment[j] = col.machine

    model.freeTransform()
    model.freeProb()

    return assignment, cost


def generate_mappings(n: int, m: int):
    p = [0 for _ in range(n)]
    while True:
        yield p

        for i in range(n):
            if p[i] + 1 == m:
                p[i] = 0
                if i + 1 == n:
                    return
            else:
                p[i] += 1
                break


def solve_enumeration(problem: GAP):
    m = len(problem.machines())
    n = len(problem.jobs())
    opt_cost = sum(problem.c[k][j]
                   for k in problem.machines() for j in problem.jobs())
    opt = None

    for p in generate_mappings(n, m):
        c = 0
        l = [0 for _ in problem.machines()]
        feasible = True
        for j, m_index in enumerate(p):
            c += problem.c[m_index][j]
            l[m_index] += problem.l[m_index][j]
            if l[m_index] > problem.w[m_index]:
                feasible = False
                break
        if not feasible:
            continue

        if c < opt_cost:
            opt_cost = c
            opt = list(p)
    if opt is None:
        raise Infeasible()
    return opt, opt_cost


def book_problem() -> GAP:
    problem = GAP(
        c=[
            [8, 3, 2, 9],
            [1, 7, 5, 2],
        ],
        l=[
            [2, 3, 3, 1],
            [5, 1, 1, 3],
        ],
        w=[5, 8],
        n=[1, 1],
    )
    return problem


def alt_problem() -> GAP:
    problem = GAP(
        c=[
            [8, 3, 2, 9, 8, 3, 2, 9],
            [1, 7, 5, 2, 1, 7, 5, 2],
            [8, 3, 2, 9, 8, 3, 2, 9],
            [1, 7, 5, 2, 1, 7, 5, 2],
        ],
        l=[
            [2, 3, 3, 1, 2, 3, 3, 1],
            [5, 1, 1, 3, 5, 1, 1, 3],
            [2, 3, 3, 1, 2, 3, 3, 1],
            [5, 1, 1, 3, 5, 1, 1, 3],
        ],
        w=[5, 8, 5, 8],
        n=[1, 1, 1, 1],
        # w=[5, 8],
        # n=[2, 2],
    )
    return problem


PROBLEMS = {
    'book': book_problem,
    'book2': alt_problem,
}

SOLVERS = {
    'bp': solve_branch_price,
    'enum': solve_enumeration,
}


def main():
    parser = ArgumentParser('gap')
    parser.add_argument('-p', '--problem', help='Problem instance',
                        default='book', choices={'book', 'book2'}, required=False)
    parser.add_argument('-s', '--solver', help='Solver',
                        default='bp', choices={'bp', 'enum'}, required=False)
    args = parser.parse_args()

    problem = PROBLEMS[args.problem]()
    solver = SOLVERS[args.solver]

    assignment, cost = solver(problem)
    print(f"ASSIGNMENT (cost = {cost}):", assignment)


if __name__ == '__main__':
    main()
