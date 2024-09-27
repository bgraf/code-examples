import tsplib95
import math
from dataclasses import dataclass
from typing import List, Tuple, Dict

import numpy as np
from numpy.typing import NDArray
from ortools.math_opt.python import mathopt
from ortools.graph.python import max_flow

import matplotlib.pyplot as plt


@dataclass
class Problem:
    nodes: List[Tuple[int, int]]
    distances: NDArray

    @property
    def size(self) -> int:
        return len(self.nodes)


def read_problem():
    raw_problem = tsplib95.load('./a280.tsp')
    nodes = [raw_problem.node_coords[p] for p in raw_problem.get_nodes()]

    n_nodes = len(nodes)
    distances = np.zeros((n_nodes, n_nodes), dtype=np.float32)

    for i in range(n_nodes):
        for j in range(i+1, n_nodes):
            distances[i, j] = distances[j, i] = math.hypot(
                nodes[i][0]-nodes[j][0], nodes[i][1] - nodes[j][1])

    return Problem(
        nodes=nodes,
        distances=distances,
    )


@dataclass
class Edge:
    t: Tuple[int, int]
    x: mathopt.Variable


def main():
    problem = read_problem()

    model = mathopt.Model(name='TSP')
    edges = [
        Edge(
            t=(i, j),
            x=model.add_integer_variable(lb=0.0, ub=1.0, name=f'X_{i}_{j}')
        )
        for i in range(problem.size)
        for j in range(i+1, problem.size)
    ]

    model.minimize(sum(e.x * problem.distances[e.t] for e in edges))

    for i in range(problem.size):
        model.add_linear_constraint(
            sum(e.x for e in edges if i in e.t) == 2)

    num_fig = 0

    def plot_tours(tours: List[List[int]]):
        nonlocal num_fig
        f, ax = plt.subplots()
        plt.title(label=f'Iteration = {num_fig+1}, #Tours = {len(tours)}')
        for tour in tours:
            x = [problem.nodes[i][0]
                 for i in tour] + [problem.nodes[tour[0]][0]]
            y = [problem.nodes[i][1]
                 for i in tour] + [problem.nodes[tour[0]][1]]

            plt.plot(x, y, "o-")

        plt.savefig(f'iteration_{num_fig:02}.png', dpi=250)
        num_fig += 1

    def subtours(values: Dict[mathopt.Variable, float]) -> List[List[int]]:
        """Transforms a MIP solution into a set of tours."""
        sol = {e.t for e in edges if values[e.x] > 0.5}

        tours = []
        while len(sol) > 0:
            _, v = sol.pop()
            tour = [v]
            while (t := next(filter(lambda t: v in t, sol), None)):
                sol.remove(t)
                v = t[0] if v == t[1] else t[1]
                tour.append(v)
            tours.append(tour)

        return tours

    def lazy_constraint_callback(data: mathopt.CallbackData) -> mathopt.CallbackResult:
        """Adds constraints to eliminate subtours."""
        res = mathopt.CallbackResult()

        # Gather all subtours from the current integer feasible solution
        tours = subtours(data.solution)
        if len(tours) == 1:
            # Only a single tour, that's great, nothing to do!
            return res

        plot_tours(tours)

        print("== got", len(tours), "subtours ==")

        # Add a constraint for each subtour
        for i, tour in enumerate(tours):
            print(f"[{i:2}] subtour:", tour)
            tour_nodes = set(tour)

            # All edges between the nodes of the subtour and the nodes not in the subtour
            cut_edges = sum(
                e.x
                for e in edges
                if (e.t[0] in tour_nodes) ^ (e.t[1] in tour_nodes)
            )

            res.add_lazy_constraint(cut_edges >= 2)

        return res

    res = mathopt.solve(
        model,
        solver_type=mathopt.SolverType.GSCIP,
        params=mathopt.SolveParameters(enable_output=True,),
        callback_reg=mathopt.CallbackRegistration(
            events={mathopt.Event.MIP_SOLUTION},
            add_lazy_constraints=True,
        ),
        cb=lazy_constraint_callback,
    )

    print(res.objective_value())
    tours = subtours(res.variable_values())
    plot_tours(tours)


if __name__ == '__main__':
    main()
