#include <algorithm>
#include <cmath>
#include <format>
#include <fstream>
#include <iostream>
#include <lemon/core.h>
#include <lemon/full_graph.h>
#include <ostream>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

#include "lemon/gomory_hu.h"
#include "lemon/list_graph.h"

#include "absl/log/check.h"
#include "absl/status/statusor.h"
#include "ortools/math_opt/cpp/math_opt.h"

namespace math_opt = ::operations_research::math_opt;

class Node
{
public:
	int id;
	int x;
	int y;
};

double distance(const Node& a, const Node& b)
{
	return std::hypot(
	  static_cast<double>(a.x - b.x), static_cast<double>(a.y - b.y));
}

using NodeList = std::vector<Node>;

static NodeList read_instance(const std::string& path)
{
	std::ifstream fp{ path };

	auto nodes = NodeList();

	int n = 0;
	fp >> n;

	for (int i = 0; i < n; i++) {
		Node node{};
		fp >> node.id >> node.x >> node.y;

		nodes.push_back(node);
	}

	fp.close();

	return nodes;
}

class Edge
{
public:
	int i;
	int j;
	math_opt::Variable var;

	bool contains(int c) const { return (c == i) || (c == j); }
};

class SolveResult
{
public:
	std::vector<int> tour;
	double cost;
};

class Solver
{
public:
	Solver(NodeList nodes);
	SolveResult Solve();

	using EdgeList = std::vector<Edge>;

private:
	NodeList nodes_;
	EdgeList edges_;
	math_opt::Model model_;

	math_opt::CallbackResult callback(math_opt::CallbackData);
	math_opt::CallbackResult callback_usercut(math_opt::CallbackData&&);
	std::vector<std::vector<int>> subtours(
	  const math_opt::VariableMap<double>&);
};

Solver::Solver(NodeList nodes)
  : nodes_(nodes)
  , edges_()
  , model_{ "TSP" }
{
	/* Build basic model */
	/* Variables */
	for (int i = 0; i < nodes_.size(); i++) {
		for (int j = i + 1; j < nodes_.size(); j++) {
			auto var = model_.AddBinaryVariable(
			  std::format("X_{}_{}", i, j));
			Edge edge{ i, j, var };
			edges_.emplace_back(std::move(edge));
		}
	}

	std::cout << "generated " << edges_.size() << " edges" << std::endl;

	/* Flow constraint for each node */
	for (int i = 0; i < nodes_.size(); i++) {
		math_opt::LinearExpression expr{};
		for (auto& edge : edges_) {
			if (edge.contains(i)) {
				expr += edge.var;
			}
		}

		model_.AddLinearConstraint(expr == 2.0);
	}

	/* Objective: minimize total distance */
	{
		math_opt::LinearExpression expr{};
		for (auto& e : edges_) {
			expr += distance(nodes_[e.i], nodes_[e.j]) * e.var;
		}

		model_.Minimize(expr);
	}
}

SolveResult Solver::Solve()
{
	math_opt::SolveArguments args{};
	args.parameters.enable_output = true;

	/* Register lazy constraint callback */
	args.callback_registration.events.emplace(
	  math_opt::CallbackEvent::kMipSolution);
	args.callback_registration.add_lazy_constraints = true;

#ifdef WITH_USER_CUTS
	/* Register user cut callback */
	args.callback_registration.events.emplace(
	  math_opt::CallbackEvent::kMipNode);
	args.callback_registration.add_cuts = true;
#endif

	args.callback = [=, this](math_opt::CallbackData data) {
		return this->callback(data);
	};

#ifdef WITH_WARMSTART
	/* Warm start with opt. tour */
	std::vector<int> initial_tour = { 1, 241, 242, 240, 239, 238, 237, 236,
		235, 234, 233, 232, 231, 230, 245, 244, 243, 246, 249, 250, 229,
		228, 227, 226, 225, 224, 223, 222, 221, 220, 219, 218, 217, 216,
		215, 214, 213, 212, 211, 210, 209, 208, 251, 252, 207, 206, 205,
		204, 203, 202, 201, 199, 143, 144, 198, 197, 200, 195, 194, 193,
		196, 192, 191, 190, 189, 188, 187, 186, 185, 184, 183, 182, 181,
		180, 175, 179, 178, 149, 177, 176, 150, 151, 155, 152, 154, 153,
		128, 129, 20, 127, 126, 125, 29, 124, 123, 122, 121, 120, 119,
		118, 156, 157, 158, 159, 174, 160, 161, 162, 163, 164, 165, 166,
		167, 168, 169, 171, 170, 172, 173, 106, 105, 104, 103, 102, 101,
		100, 99, 98, 97, 96, 95, 94, 93, 92, 91, 90, 89, 88, 108, 107,
		109, 110, 111, 87, 86, 112, 113, 114, 116, 115, 85, 84, 83, 82,
		81, 80, 79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66,
		65, 64, 63, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45,
		44, 43, 58, 62, 61, 117, 60, 59, 42, 41, 40, 39, 38, 37, 36, 35,
		34, 33, 32, 31, 30, 28, 27, 26, 25, 21, 24, 22, 23, 13, 14, 12,
		11, 10, 9, 8, 7, 6, 5, 4, 3, 276, 275, 274, 273, 272, 271, 270,
		15, 16, 17, 18, 19, 130, 131, 132, 133, 269, 268, 134, 135, 267,
		266, 136, 137, 138, 148, 147, 146, 145, 142, 141, 140, 139, 265,
		264, 263, 262, 261, 260, 259, 258, 257, 256, 253, 254, 255, 248,
		247, 277, 278, 2, 279, 0, 1 };

	math_opt::ModelSolveParameters::SolutionHint hint{};
	for (const auto& e : edges_) {
		hint.variable_values.emplace(e.var, 0.0);
	}

	for (int p = 0; p < initial_tour.size() - 1; p++) {
		auto n1 = initial_tour[p];
		auto n2 = initial_tour[p + 1];
		if (n2 < n1) {
			std::swap(n1, n2);
		}

		for (const auto& e : edges_) {
			if (e.i == n1 && e.j == n2) {
				hint.variable_values.at(e.var) = 1.0;
				break;
			}
		}
	}

	args.model_parameters.solution_hints.emplace_back(std::move(hint));
#endif

	const absl::StatusOr<math_opt::SolveResult> result =
	  math_opt::Solve(model_, math_opt::SolverType::kGscip, args);

	if (!result->termination.IsOptimal()) {
		throw std::runtime_error("did not solve to optimality");
	}

	return SolveResult{ subtours(result->variable_values()).at(0),
		result->objective_value() };
}

std::vector<std::vector<int>> Solver::subtours(
  const math_opt::VariableMap<double>& vm)
{
	std::set<int> active_edges{};
	for (int e = 0; e < edges_.size(); e++) {
		const Edge& edge = edges_[e];
		if (vm.at(edge.var) > 0.5) {
			/* Edge contained in integer solution */
			active_edges.insert(e);
		}
	}

	std::vector<std::vector<int>> tours{};

	while (!active_edges.empty()) {
		auto e = *active_edges.begin();
		active_edges.erase(e);
		auto v = edges_[e].j;

		std::vector<int> tour{};
		tour.push_back(v);

		while (true) {
			auto res = std::find_if(active_edges.begin(),
			  active_edges.end(), [this, v](auto id) {
				  const auto& edge = edges_[id];
				  return edge.contains(v);
			  });

			if (res == active_edges.end()) {
				break;
			}

			auto e = (*res);
			active_edges.erase(e);
			auto& edge_f = edges_[e];
			v = edge_f.i == v ? edge_f.j : edge_f.i;
			tour.push_back(v);
		}

		tours.emplace_back(std::move(tour));
	}

	return tours;
}

math_opt::CallbackResult Solver::callback(math_opt::CallbackData data)
{
#ifdef WITH_USER_CUTS
	/* MIP Node event */
	if (data.event == math_opt::CallbackEvent::kMipNode) {
		return callback_usercut(std::move(data));
	}
#endif

	if (!data.solution.has_value()) {
		return {};
	}

	auto tours = subtours(*data.solution);

	std::cout << std::format(
	  "!! Lazy-Callback: got {} tours\n", tours.size());

	if (tours.size() <= 1) {
		return {};
	}

	math_opt::CallbackResult result{};

	std::vector<bool> in_tour(nodes_.size(), false);
	for (const auto& tour : tours) {
		std::fill(in_tour.begin(), in_tour.end(), false);
		for (auto i : tour) {
			in_tour[i] = true;
		}

		math_opt::LinearExpression expr{};
		for (const auto& e : edges_) {
			if (in_tour[e.i] ^ in_tour[e.j]) {
				expr += e.var;
			}
		}

		result.AddLazyConstraint(expr >= 2.0);

		if (tours.size() == 2) {
			break;
		}
	}

	return result;
}

math_opt::CallbackResult Solver::callback_usercut(math_opt::CallbackData&& data)
{
	if (!data.solution.has_value()) {
		return {};
	}

	/* Build graph of current LP solution */
	auto g = lemon::ListGraph();
	auto emap = decltype(g)::EdgeMap<double>(g);

	using Node = decltype(g)::Node;

	/* Nodemap: maps each node [0, n) to its lemon representation "Node" */
	std::vector<Node> nodemap(nodes_.size(), lemon::INVALID);
	for (int i = 0; i < nodes_.size(); i++) {
		nodemap[i] = g.addNode();
	}

	for (const auto& e : edges_) {
		double value =
		  std::round(data.solution->at(e.var) * 10000.0) / 10000.0;

		if (value > 0.0) {
			auto edge = g.addEdge(nodemap[e.i], nodemap[e.j]);
			emap.set(edge, value);
		}
	}

	/* Calculate Gomory-Hu tree */
	auto gh = lemon::GomoryHu<decltype(g), decltype(emap)>(g, emap);
	gh.run();

	/* Find minimum min-cut among n-1 cuts */
	double best_mincut = 10.0;
	Node node_i = lemon::INVALID;
	Node node_j = lemon::INVALID;
	for (int i = 0; i < nodes_.size(); i++) {
		const auto node = nodemap[i];
		const auto pred = gh.predNode(node);
		if (pred == lemon::INVALID) {
			continue;
		}

		const auto val = gh.minCutValue(node, pred);
		if (val < best_mincut) {
			best_mincut = val;
			node_i = node;
			node_j = pred;
		}
	}

	math_opt::CallbackResult result{};

	/* Add cutting plane if there's a violation */
	if (best_mincut <= 1.9) {
		/* Node bipartition in front and behind the minimum cut */
		decltype(g)::NodeMap<bool> cutMap(g);
		gh.minCutMap(node_i, node_j, cutMap);

		math_opt::LinearExpression expr{};
		for (const auto& e : edges_) {
			if (cutMap[nodemap[e.i]] ^ cutMap[nodemap[e.j]]) {
				expr += e.var;
			}
		}

		result.AddUserCut(expr >= 2.0);
	}

	return result;
}

int main()
{
	auto nodes = read_instance("instance.tsp");

	auto solver = Solver(nodes);
	auto result = solver.Solve();

	std::cout << "Tour:";
	for (auto i : result.tour) {
		std::cout << " " << i;
	}
	std::cout << std::endl;
	std::cout << "final tour has cost: " << result.cost << std::endl;
}