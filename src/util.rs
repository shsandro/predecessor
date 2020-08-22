use fera::fun::vec;
use fera::graph::algs::Kruskal;
use fera::graph::prelude::*;
use rand::prelude::*;
use rand::XorShiftRng;

pub fn new_rng_with_seed(x: u32) -> XorShiftRng {
    let b1: u8 = ((x >> 24) & 0xff) as u8;
    let b2: u8 = ((x >> 16) & 0xff) as u8;
    let b3: u8 = ((x >> 8) & 0xff) as u8;
    let b4: u8 = (x & 0xff) as u8;
    XorShiftRng::from_seed([
        b1, b2, b3, b4, b1, b2, b3, b4, b1, b2, b3, b4, b1, b2, b3, b4,
    ])
}

// returns a list of random tree edges from the Kruskal's algorithm
pub fn kruskal_random_tree(g: &StaticGraph) -> Vec<Edge<StaticGraph>> {
    let mut rng = new_rng_with_seed(random());
    let mut edges = vec(g.edges());
    let mut tree = vec![];

    rng.shuffle(&mut edges);
    tree.clear();
    tree.extend(g.kruskal().edges(&edges));

    tree
}

// executes the reduction from Hamilton Cycle to Hamilton Path
pub fn reduction(g: &StaticGraph) -> StaticGraph {
    let n: usize = g.num_vertices();
    let v_: usize = n;
    let s: usize = n + 1;
    let t: usize = n + 2;
    let mut builder = StaticGraph::builder(n + 3, 0);

    //make a copy of the graph g
    for e in g.edges() {
        let u = g.source(e);
        let v = g.target(e);
        builder.add_edge(u as usize, v as usize);
    }

    let v: usize = 0;

    //make v' a "copy" of v
    for u in g.out_neighbors(v as u32) {
        builder.add_edge(u as usize, v_);
    }

    //add the reduction's edges
    builder.add_edge(s, v);
    builder.add_edge(v_, t);
    builder.add_edge(v, v_);

    let g_ = builder.finalize();

    assert_eq!(
        g_.num_edges(),
        g.num_edges() + g.out_degree(v as u32) + 3,
        "The reduction is wrong"
    );

    g_
}
