import networkx as nx


def gusfields_cut_tree(G: nx.Graph):
    # == Initialization ==

    nodes = list(G.nodes())

    # Choose an arbitary root node
    root = nodes[0]

    # pred[n] is the parent of n in T.
    # The root doesn't have a parent, all other nodes are children of root.
    pred = [root for _ in nodes]
    pred[root] = None

    # weight[n] is the weight of edge { n, parent(n) } in T.
    # The root doesn't have a weight, all other nodes have zero weight initially.
    weight = [0 for _ in nodes]
    weight[root] = None

    # == Calculation ==

    for n in nodes:
        if n == root:
            continue

        # Minimum cut between n and parent(n)
        pn = pred[n]
        cut_value, (source_side, _) = nx.minimum_cut(G, n, pn)
        weight[n] = cut_value

        # All siblings of n on n's side of the cut will become n's children.
        # The remaining siblings stay with parent(n).
        for nn in source_side:
            if nn != n and pred[nn] == pn:
                pred[nn] = n

        # If n's grandparent is actually on n's side of the cut, n and its parent
        # swap places.
        if pred[pn] is not None and pred[pn] in source_side:
            pred[n] = pred[pn]
            pred[pn] = n
            weight[n] = weight[pn]
            weight[pn] = cut_value

    # == Result ==

    T = nx.Graph()
    for (i, p) in enumerate(pred):
        if p is None:
            continue
        T.add_edge(i, p, weight=weight[i])
    return T


def main():
    edges = [
        (0, 1, 1),
        (0, 2, 7),
        (1, 2, 1),
        (1, 3, 3),
        (1, 4, 2),
        (2, 4, 4),
        (3, 4, 1),
        (3, 5, 6),
        (4, 5, 2),
    ]

    G = nx.Graph()
    for (v, w, c) in edges:
        G.add_edge(v, w, capacity=c)

    tree = gusfields_cut_tree(G)
    print(tree)


if __name__ == '__main__':
    main()
