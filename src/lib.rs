/*
Predecessor Array for tree representation
*/
mod util;

use fera::graph::algs::trees::Trees;
use fera::graph::prelude::*;
use fera::graph::traverse::{Control, Dfs, OnDiscoverTreeEdge};
use rand::random;
use rand::Rng;
use std::fmt;
use std::mem::replace;

#[derive(Debug)]
pub enum PredecessorError {
    EmptyGraph,
    NotTreeEdges,
}

impl fmt::Display for PredecessorError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PredecessorError::EmptyGraph => write!(f, "The graph has no vertex."),
            PredecessorError::NotTreeEdges => write!(f, "The edges do not build a tree."),
        }
    }
}

#[derive(Clone, Debug)]
pub struct PredecessorArray<'a> {
    pred: DefaultVertexPropMut<StaticGraph, OptionVertex<StaticGraph>>,
    pub g: &'a StaticGraph,
}

impl<'a> fmt::Display for PredecessorArray<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (write!(f, "Graph\n"))?;
        for e in self.g.edges() {
            (write!(f, "{} -> {}\n", self.g.source(e), self.g.target(e)))?;
        }

        (write!(f, "\nTree\n"))?;
        for v in self.g.vertices() {
            if let Some(pred) = self.parent(v) {
                (write!(f, "{} -> {}\n", pred, v))?;
            } else {
                (write!(f, "Root({})\n", v))?;
            }
        }

        Ok(())
    }
}

impl<'a> PartialEq for PredecessorArray<'a> {
    fn eq(&self, other: &Self) -> bool {
        if self.g == other.g {
            for u in self.g.vertices() {
                if let Some(v) = self.parent(u) {
                    let e = self.g.edge_by_ends(u, v);
                    if !other.contains(e) {
                        return false;
                    }
                }
            }

            true
        } else {
            false
        }
    }
}

impl<'a> PredecessorArray<'a> {
    pub fn kruskal_random_tree(g: &'a StaticGraph) -> Result<Self, PredecessorError> {
        if let Some(_) = g.vertices().next() {
            let sub_edges = util::kruskal_random_tree(g);

            PredecessorArray::from_edges(g, &sub_edges)
        } else {
            Err(PredecessorError::EmptyGraph)
        }
    }

    pub fn from_edges(
        g: &'a StaticGraph,
        edges: &[Edge<StaticGraph>],
    ) -> Result<Self, PredecessorError> {
        if let Some(root) = g.vertices().next() {
            let sub = g.spanning_subgraph(edges);

            if sub.is_tree() {
                let mut pred = g.default_vertex_prop(StaticGraph::vertex_none());

                sub.dfs(OnDiscoverTreeEdge(|e| {
                    let u = sub.source(e);
                    let v = sub.target(e);

                    pred[v] = Some(u).into();
                    Control::Continue
                }))
                .roots(vec![root])
                .run();

                Ok(PredecessorArray { pred, g })
            } else {
                Err(PredecessorError::NotTreeEdges)
            }
        } else {
            Err(PredecessorError::EmptyGraph)
        }
    }

    fn set_pred(
        &mut self,
        u: Vertex<StaticGraph>,
        predecessor: OptionVertex<StaticGraph>,
    ) -> Option<Vertex<StaticGraph>> {
        replace(&mut self.pred[u], predecessor).into_option()
    }

    fn cut_pred(&mut self, u: Vertex<StaticGraph>) -> Option<Vertex<StaticGraph>> {
        replace(&mut self.pred[u], StaticGraph::vertex_none()).into_option()
    }

    pub fn make_root(&mut self, v: Vertex<StaticGraph>) {
        let mut pred = self.cut_pred(v);
        let mut cur = v;

        while let Some(p) = pred {
            pred = self.set_pred(p, cur.into());
            cur = p;
        }
    }

    pub fn parent(&self, v: Vertex<StaticGraph>) -> Option<Vertex<StaticGraph>> {
        self.pred[v].into_option()
    }

    pub fn neighbors(&self, v: Vertex<StaticGraph>) -> Vec<Vertex<StaticGraph>> {
        let mut neighbors: Vec<Vertex<StaticGraph>> = Vec::new();

        if let Some(root) = self.parent(v) {
            neighbors.push(root);
        }

        for u in self.g.vertices() {
            if let Some(pred) = self.parent(u) {
                if pred == v {
                    neighbors.push(u);
                }
            }
        }

        neighbors
    }

    pub fn is_root(&self, v: Vertex<StaticGraph>) -> bool {
        self.pred[v].into_option().is_none()
    }

    pub fn is_ancestor(&self, ancestor: Vertex<StaticGraph>, v: Vertex<StaticGraph>) -> bool {
        let mut cur = Some(v);

        while let Some(p) = cur {
            if p == ancestor {
                return true;
            }
            cur = self.parent(p);
        }

        false
    }

    pub fn is_pred(&self, pred: Vertex<StaticGraph>, v: Vertex<StaticGraph>) -> bool {
        if let Some(p) = self.parent(v) {
            p == pred
        } else {
            false
        }
    }

    pub fn contains(&self, e: Edge<StaticGraph>) -> bool {
        let u = self.g.source(e);
        let v = self.g.target(e);

        self.is_pred(u, v) || self.is_pred(v, u)
    }

    fn distinct_tree(&self, u: Vertex<StaticGraph>, v: Vertex<StaticGraph>) -> bool {
        let mut u_root = u;

        while let Some(pred) = self.parent(u_root) {
            u_root = pred;
        }

        let mut v_root = v;

        while let Some(pred) = self.parent(v_root) {
            v_root = pred;
        }

        u_root != v_root
    }

    // TODO: melhorar testes para change_edges
    pub fn change_edges(&mut self, ins: Edge<StaticGraph>, rem: Edge<StaticGraph>) -> bool {
        // aresta a ser inserida não pode estar na árvore
        let (u, v) = if !self.contains(ins) {
            (self.g.source(ins), self.g.target(ins))
        } else {
            return false;
        };

        // aresta a ser removida tem que estar na árvore
        let (s, t) = if self.contains(rem) {
            (self.g.source(rem), self.g.target(rem))
        } else {
            return false;
        };

        let (parent, w) = if self.is_pred(s, t) {
            // se s é predecessor de t, remove pred de t e insere a nova aresta
            (s, t)
        } else {
            (t, s)
        };

        self.cut_pred(w);

        // verifica se a nova aresta conecta a árvore
        if self.distinct_tree(u, v) {
            self.make_root(v);

            self.set_pred(v, u.into());

            true
        } else {
            self.set_pred(w, parent.into());
            false
        }
    }

    pub fn change_pred(
        &mut self,
        ins: Edge<StaticGraph>,
    ) -> Option<(Edge<StaticGraph>, Edge<StaticGraph>)> {
        // aresta a ser inserida não pode estar na árvore
        if !(self.contains(ins)) {
            let u = self.g.source(ins);
            let v = self.g.target(ins);

            let random = rand::thread_rng().gen_range(0, 10);

            let (ancestor, w) = if self.is_ancestor(u, v) {
                (u, v)
            } else if self.is_ancestor(v, u) {
                (v, u)
            } else if random % 2 == 0 {
                (u, v)
            } else {
                (v, u)
            };

            if let Some(pred) = self.set_pred(w, ancestor.into()) {
                let rem = self.g.edge_by_ends(pred, w);
                Some((ins, rem))
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn change_any(
        &mut self,
        ins: Edge<StaticGraph>,
    ) -> Option<(Edge<StaticGraph>, Edge<StaticGraph>)> {
        // aresta a ser inserida não pode estar na árvore
        if !(self.contains(ins)) {
            let u = self.g.source(ins);
            let v = self.g.target(ins);

            self.make_root(u);

            let e = self.choose_through_path(v);
            let x = self.g.target(e);
            let pred_x = self.g.source(e);

            self.set_pred(u, v.into());
            self.cut_pred(x);

            let rem = self.g.edge_by_ends(pred_x, x);

            Some((ins, rem))
        } else {
            None
        }
    }

    // choose a random vertex from u to root
    fn choose_through_path(&self, u: Vertex<StaticGraph>) -> Edge<StaticGraph> {
        let path = self.path_to_root(u);

        let mut rng = util::new_rng_with_seed(random());
        let i = rng.gen_range(0, path.len());

        let x = path[i];
        let pred_x = self.parent(x).unwrap();

        return self.g.edge_by_ends(pred_x, x);
    }

    // build a vec that contains the vertex chain from u to root (not containing the root)
    fn path_to_root(&self, u: Vertex<StaticGraph>) -> Vec<Vertex<StaticGraph>> {
        let mut cur = u;
        let mut path = Vec::new();

        while let Some(pred) = self.parent(cur) {
            path.push(cur);
            cur = pred;
        }

        path
    }

    #[cfg(test)]
    // check if a predecessor array is consistent
    pub fn check(&self) {
        let mut edges: Vec<Edge<StaticGraph>> = Vec::new();

        for u in self.g.vertices() {
            if let Some(v) = self.parent(u) {
                if let Some(e) = self.g.get_edge_by_ends(u, v) {
                    edges.push(e);
                } else {
                    panic!()
                }
            } else {
                assert!(self.is_root(u));
            }
        }

        let tree = self.g.spanning_subgraph(&edges);
        assert!(tree.is_tree());
    }

    #[cfg(test)]
    // return the tree root
    // used only for test of PredecessorArray::distinct_tree in the test module
    fn root(&self) -> Vertex<StaticGraph> {
        let mut cur = self.g.vertices().next().unwrap();

        while let Some(pred) = self.parent(cur) {
            cur = pred;
        }

        cur
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::*;
    use fera::graph::choose::Choose;
    use rand::random;

    #[test]
    fn partial_eq() {
        for _ in 0..1000 {
            let rng = new_rng_with_seed(random());
            let g: StaticGraph = StaticGraph::new_gn_connected(50, rng);
            let pred = PredecessorArray::kruskal_random_tree(&g);

            if let Ok(p) = pred {
                assert!(p == p);
            } else {
                panic!();
            }
        }

        for _ in 0..1000 {
            let rng = new_rng_with_seed(random());
            let g: StaticGraph = StaticGraph::new_gn_connected(50, rng.clone());
            let pred = PredecessorArray::kruskal_random_tree(&g);

            if let Ok(p) = pred {
                let mut p_clone = p.clone();
                let e = p_clone.g.choose_edge(rng).unwrap();

                if let Some((_, _)) = p_clone.change_any(e) {
                    assert!(p != p_clone);
                } else {
                    assert!(p == p_clone);
                }
            } else {
                panic!();
            }
        }

        for _ in 0..1000 {
            let rng = util::new_rng_with_seed(random());
            let g = StaticGraph::new_random_tree(30, rng);
            let g_ = StaticGraph::new_complete(30);
            let edges = util::kruskal_random_tree(&g);
            let pred = PredecessorArray::from_edges(&g, &edges);
            let pred_ = PredecessorArray::from_edges(&g_, &edges);

            if let Ok(p) = pred {
                if let Ok(p_) = pred_ {
                    assert!(p != p_);
                }
            } else {
                panic!()
            }
        }
    }
    #[test]
    // check if the edges into the predecessor array are valid or if a vertex is root
    // check if the edges in the predecessor array builds a tree
    fn kruskal_random_tree() {
        for _ in 0..1000 {
            let rng = new_rng_with_seed(random());
            let g: StaticGraph = StaticGraph::new_gn_connected(20, rng);
            let pred = PredecessorArray::kruskal_random_tree(&g);

            if let Ok(p) = pred {
                p.check();
            } else {
                panic!();
            }
        }
    }

    #[test]
    fn kruskal_random_tree_erros() {
        let g = StaticGraph::new_empty(0);
        let p = PredecessorArray::kruskal_random_tree(&g);

        if let Err(e) = p {
            println!("{}", e);
        } else {
            panic!();
        }

        for i in 2..100 {
            let rng = new_rng_with_seed(random());
            let g = StaticGraph::new_gnm(i, i - 2, rng).unwrap();
            let p = PredecessorArray::kruskal_random_tree(&g);

            if let Err(e) = p {
                println!("{}", e);
            } else {
                panic!();
            }
        }
    }

    #[test]
    fn from_edges() {
        for _ in 0..1000 {
            let rng = util::new_rng_with_seed(random());
            let g = StaticGraph::new_random_tree(30, rng);
            let edges = util::kruskal_random_tree(&g);
            let pred = PredecessorArray::from_edges(&g, &edges);

            if let Ok(p) = pred {
                p.check();
            } else {
                panic!()
            }
        }
    }

    #[test]
    fn from_edges_errors() {
        let g = StaticGraph::new_empty(0);
        let edges = [];
        let instance = PredecessorArray::from_edges(&g, &edges);

        if let Err(e) = instance {
            println!("{}", e);
        } else {
            panic!();
        }

        let g = StaticGraph::new_empty(2);
        let instance = PredecessorArray::from_edges(&g, &edges);

        if let Err(e) = instance {
            println!("{}", e);
        } else {
            panic!();
        }

        for i in 2..100 {
            let rng = util::new_rng_with_seed(random());
            let g = StaticGraph::new_gnm(i, i - 2, rng).unwrap();
            let edges = util::kruskal_random_tree(&g);
            let instance = PredecessorArray::from_edges(&g, &edges);

            if let Err(e) = instance {
                println!("{}", e);
            } else {
                panic!();
            }
        }
    }

    #[test]
    // check the consistency of make_root function
    fn make_root() {
        for _ in 0..1000 {
            let rng = new_rng_with_seed(random());
            let g: StaticGraph = StaticGraph::new_gn_connected(30, rng);
            let p = PredecessorArray::kruskal_random_tree(&g);

            if let Ok(mut p) = p {
                for v in g.vertices() {
                    p.make_root(v);
                    assert!(p.is_root(v));
                    p.check();
                }
            } else {
                panic!();
            }
        }
    }

    #[test]
    fn is_ancestor() {
        for _ in 0..1000 {
            let rng = new_rng_with_seed(random());
            let g: StaticGraph = StaticGraph::new_gn_connected(30, rng.clone());
            let p = PredecessorArray::kruskal_random_tree(&g);

            if let Ok(p) = p {
                let root = p.root();

                for v in g.vertices() {
                    assert!(p.is_ancestor(v, v));
                    assert!(p.is_ancestor(root, v));
                }
            } else {
                panic!();
            }
        }
    }

    #[test]
    fn distinct_tree() {
        for _ in 0..1000 {
            let rng = new_rng_with_seed(random());
            let g: StaticGraph = StaticGraph::new_random_tree(30, rng.clone());
            let pred = PredecessorArray::kruskal_random_tree(&g);

            if let Ok(mut p) = pred {
                let root = p.root();
                if let Some(v) = g.choose_vertex(rng) {
                    if let Some(pred_v) = p.cut_pred(v) {
                        assert!(p.distinct_tree(v, root));

                        for s in g.out_neighbors(v) {
                            if s != pred_v {
                                for t in g.out_neighbors(root) {
                                    if t != v && t != s {
                                        assert!(p.distinct_tree(s, t));
                                    }
                                }
                            }
                        }
                    } else {
                        assert!(!p.distinct_tree(v, root));
                    }
                }
            } else {
                panic!();
            }
        }
    }

    #[test]
    fn change_edges() {
        for _ in 0..1000 {
            let rng = new_rng_with_seed(random());
            let rng2 = new_rng_with_seed(random());

            let g: StaticGraph = StaticGraph::new_gn_connected(20, rng.clone());
            let pred = PredecessorArray::kruskal_random_tree(&g);

            if let Ok(mut p) = pred {
                let ins = g.choose_edge(rng.clone()).unwrap();
                let rem = g.choose_edge(rng2.clone()).unwrap();

                p.change_edges(ins, rem);

                p.check();
            } else {
                panic!();
            }
        }
    }
}
