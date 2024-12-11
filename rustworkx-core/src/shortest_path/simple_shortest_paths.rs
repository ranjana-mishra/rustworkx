// Licensed under the Apache License, Version 2.0 (the "License"); you may
// not use this file except in compliance with the License. You may obtain
// a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.

use crate::petgraph::algo::{Measure};
use crate::petgraph::graph::{Graph, Node, NodeIndex};
use crate::petgraph::visit::{EdgeRef, IntoEdges, VisitMap, Visitable, IntoEdgeReferences};
use crate::petgraph::EdgeType;

//use min_scored::MinScored;

use std::cmp::Ordering;
use std::vec::IntoIter;
use std::collections::hash_map::Entry::{Occupied, Vacant};
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::collections::hash_map::Entry;
use std::fmt::Debug;
use std::hash::Hash;
use std::f32;
use std::iter::Map;
use petgraph::data::DataMap;
use petgraph::graph::{Edge, EdgeIndex, EdgeReference, GraphIndex};
use petgraph::Undirected;
use petgraph::visit::{GraphBase, GraphRef};
use rand::Rng;
use crate::min_scored::MinScored;
use crate::traversal::dijkstra_search;

/// This is mutation of petgraph dijkastra to get all possible parents_nodes for a target instead of shortest only
/// Returns the default score Hashmap also a set of (parent_node, node, score) vector.

fn dijkstra<G, F, K>(
    graph: G,
    start: G::NodeId,
    goal: Option<G::NodeId>,
    mut edge_cost: F, 
) -> (HashMap<G::NodeId, K>, Vec<(G::NodeId, G::NodeId,K)>)
where
    G: IntoEdges + Visitable,
    G::NodeId: Eq + Hash,
    F: FnMut(G::EdgeRef) -> K,
    K: Measure + Copy,
    <G>::NodeId: Debug, <G as IntoEdgeReferences>::EdgeRef: PartialEq
{
    let mut visited = graph.visit_map();
    let mut scores = HashMap::new();
    let mut visit_next = BinaryHeap::new();
    let zero_score = K::default();
    scores.insert(start, zero_score);
    let mut tracing: Vec<(G::NodeId, G::NodeId,K)> = vec!();
    visit_next.push(MinScored(zero_score, start));
    while let Some(MinScored(node_score, node)) = visit_next.pop() {
        if visited.is_visited(&node) {
            continue;
        }
        if goal.as_ref() == Some(&node) {
            break;
        }
        for edge in graph.edges(node) {
            let next = edge.target();
            if visited.is_visited(&next) {
                continue;
            }
            let next_score = node_score + edge_cost(edge);
            match scores.entry(next) {
                Occupied(ent) => {
                    if next_score < *ent.get() {
                        *ent.into_mut() = next_score;
                        visit_next.push(MinScored(next_score, next));
                        tracing.push((next, node,next_score));
                        }
                     else {
                        tracing.push((next, node, next_score));
                    }
                }
                Vacant(ent) => {
                    ent.insert(next_score);
                    visit_next.push(MinScored(next_score, next));
                    tracing.push((next, node,next_score));
                }
            }
        }
        visited.visit(node);
    }
    (scores, tracing)
}

#[derive(Debug)]
struct PathNode<N, K>
{
    pub node_id: N,                         // node identifier
    pub num_paths: usize,                   // number of paths with min cost ending at the node
    pub parents: Vec<N>,                    // parents along min cost path
    pub cost: K                             // minimum cost associated to the node (cost of all the paths ending here).
}

#[derive(Debug)]
struct NodeData<N, K>
{
    pub node_id: N,                             // node identifier
    pub parent_id: Option<N>,                   // parent identifier
    pub cost: K,                                // cost of minimum path from source
}

pub fn get_paths<N, K>(
    pathnodes: &HashMap<N, PathNode<N,K>>,
    start:&N,
    target:&N,
    num_paths:usize
) -> Vec<Vec<N>>
where N: Eq + Hash + Clone
{
    if start == target {
        return vec![vec![start.clone()]];
    }

    let mut remaining_paths = num_paths;
    let target_node = pathnodes.get(target).unwrap();
    let mut collect_paths = target_node.parents.iter().map(|p| {
        let p_node = pathnodes.get(p).unwrap();
        if remaining_paths > 0 {
            let num_paths_p = if remaining_paths > p_node.num_paths {
                p_node.num_paths
            } else {
                remaining_paths
            };
            remaining_paths = remaining_paths - num_paths_p;
            get_paths(pathnodes, start, p, num_paths_p)
        } else {
            vec![]
        }
    }).collect::<Vec<_>>();

    let mut all_paths: Vec<Vec<N>> = vec![];
    for i in 0.. collect_paths.len() {
        all_paths.append(&mut collect_paths[i]);
    }

    for i in 0.. all_paths.len() {
        all_paths[i].push(target.clone());
    }

    all_paths
}
/// Djikstra's algorithm modified to find k paths of minimum length between vertices s and t.
/// The algorithm returns k paths from source to target if they exist, else it returns the maximum
/// number of shortest paths between s and t.
pub fn dijkstra_k_shortest_paths<G, F, K>(
    graph: G,
    start: G::NodeId,
    target: G::NodeId,
    mut edge_cost:F,
    max_paths: usize,
) -> (Vec<Vec<G::NodeId>>, K)
where
    G: Visitable + IntoEdges,
    G::NodeId: Eq + Hash,
    F: FnMut(G::EdgeRef) -> K,
    K: Measure + Copy,
    G::NodeId: Debug, <G as IntoEdgeReferences>::EdgeRef: PartialEq
{
    let mut visit_map = graph.visit_map();
    let mut scores: HashMap<G::NodeId, K> = HashMap::new();
    let mut pathnodes: HashMap<G::NodeId, PathNode<G::NodeId,K>> = HashMap::new();
    let mut visit_next: BinaryHeap<MinScored< K, <G as GraphBase>::NodeId> > = BinaryHeap::new();
    visit_next.push(MinScored(K::default(), start));
    scores.insert(start, K::default());
    pathnodes.insert(start, PathNode {
        node_id: start,
        num_paths: 1,
        parents: vec![],
        cost: K::default()
    });

    // In the loop below, all the nodes which have been assigned the shortest path from source
    // are marked as visited. The visisted nodes are not present in the heap, and hence we do not
    // consider edges to visited nodes.
    while let Some(MinScored(node_score, node)) = visit_next.pop() {
        visit_map.visit(node);

        // traverse the unvisited neighbors of node.
        for edge in graph.edges(node) {
            let edge_weight = edge_cost(edge);
            let v = edge.target();
            if visit_map.is_visited(&v) {
                continue;
            }

            match scores.entry(v) {
                Occupied(mut ent) => {
                    if node_score + edge_weight < *ent.get() {
                        // the node leads to shorter path to v. We update the score in the priority heap
                        // Since this parent defines the new shortest path, we create a fresh entry in pathnodes
                        // with this parent, discarding any earlier entry with other parent(s).
                        scores.insert(v, node_score + edge_weight);
                        visit_next.push(MinScored(node_score + edge_weight, v));
                        if let Some(v_pnode) = pathnodes.get(&v) {
                            let node_num_paths = pathnodes.get(&node).unwrap().num_paths;
                            let new_node: PathNode<G::NodeId, K> = PathNode {
                                node_id: v_pnode.node_id,
                                num_paths: node_num_paths,
                                parents: vec![node],
                                cost: node_score + edge_weight,
                            };
                         pathnodes.insert(v_pnode.node_id, new_node);

                        } else {
                            assert_eq!(true, false, "Invariant not satisfied, Node {:?} not present in pathnodes", v);
                        }
                    } else if node_score + edge_weight == *ent.get() {
                        // node leads to a new shortest path.
                        // update the entry in the pathnodes map
                        let node_num_paths = pathnodes.get(&node).unwrap().num_paths;
                        if let Some(v_pnode) = pathnodes.get(&v) {
                            if v_pnode.num_paths < max_paths {
                                let mut new_node: PathNode<G::NodeId, K> = PathNode {
                                    node_id: v_pnode.node_id,
                                    num_paths: v_pnode.num_paths,
                                    parents: v_pnode.parents.clone(),
                                    cost: node_score + edge_weight,
                                };
                                new_node.parents.push(node);
                                new_node.num_paths += node_num_paths;
                                pathnodes.insert(v, new_node);
                            }

                        } else {
                            assert_eq!(true, false, "Invariant not satisfied, Node {:?} not present in pathnodes", v);
                        }
                    } else {
                        // do nothing
                    }
                }
                Vacant(_) => {
                    // the node v has no entry in the priority queue so far.
                    // We must be visiting it the first time.
                    // Create the entry in the priority queue and an entry in the pathnodes map.
                    scores.insert(v, node_score + edge_weight);
                    visit_next.push(MinScored(node_score + edge_weight, v));
                    let node_num_paths = pathnodes.get(&node).unwrap().num_paths;
                    pathnodes.insert(v, PathNode {
                        node_id: v,
                        num_paths: node_num_paths,
                        parents: vec![node],
                        cost: node_score + edge_weight
                    });
                }
            }
        }
    }

    //println!("Pathnodes = {:?}", pathnodes);
    let min_cost = pathnodes.get(&target).unwrap().cost;
    println!("Number of shortest paths from {:?} to {:?} = {}", start, target, pathnodes.get(&target).unwrap().num_paths);
    println!("Cost of minimum path = {:?}", min_cost);

    // Now return at most max_paths
    let mut shortest_path: Vec<G::NodeId> = Vec::new();
    if let Some(target_node) = pathnodes.get(&target) {
        /*
        let num_paths = if max_paths < target_node.num_paths {
            max_paths
        } else {
            target_node.num_paths
        };

        println!("Num paths = {}", num_paths);
        let paths_vec = get_paths(&pathnodes, &start, &target, num_paths);
        (paths_vec, min_cost)

         */

        // Let us just return one shortest path
        let mut current_node = target_node;
        shortest_path.push(current_node.node_id);
        while current_node.node_id != start {
            current_node = pathnodes.get(&current_node.parents[0]).unwrap();
            shortest_path.push(current_node.node_id);
        }
        shortest_path.reverse();
        (vec![shortest_path], min_cost)

    } else {
        (vec![], K::default())
    }
}

pub fn dijkstra_shortest_path_with_excluded_prefix<G, F, K>(
    graph: G,
    start: G::NodeId,
    target: G::NodeId,
    mut edge_cost:F,
    excluded_prefix: &HashSet<G::NodeId>,
) -> (Vec<G::NodeId>, K)
where
    G: Visitable + IntoEdges,
    G::NodeId: Eq + Hash,
    F: FnMut(G::EdgeRef) -> K,
    K: Measure + Copy,
    G::NodeId: Debug, <G as IntoEdgeReferences>::EdgeRef: PartialEq
{
    let mut visit_map = graph.visit_map();
    let mut scores: HashMap<G::NodeId, K> = HashMap::new();
    let mut pathnodes: HashMap<G::NodeId, NodeData<G::NodeId,K>> = HashMap::new();
    let mut visit_next: BinaryHeap<MinScored< K, G::NodeId> > = BinaryHeap::new();
    visit_next.push(MinScored(K::default(), start));
    scores.insert(start, K::default());
    pathnodes.insert(start, NodeData {
        node_id: start,
        parent_id: None,
        cost: K::default()
    });

    // In the loop below, all the nodes which have been assigned the shortest path from source
    // are marked as visited. The visisted nodes are not present in the heap, and hence we do not
    // consider edges to visited nodes.
    while let Some(MinScored(node_score, node)) = visit_next.pop() {
        visit_map.visit(node);

        // traverse the unvisited neighbors of node.
        for edge in graph.edges(node) {
            let v = edge.target();

            // don't traverse the nodes marked for exclusion, or which have been visited.
            if visit_map.is_visited(&v) || excluded_prefix.contains(&v){
                continue;
            }

            let edge_weight = edge_cost(edge);
            match scores.entry(v) {
                Occupied(mut ent) => {
                    if node_score + edge_weight < *ent.get() {
                        // the node leads to shorter path to v. We update the score in the priority heap
                        // Since this parent defines the new shortest path, we update the entry in pathnodes
                        // with this parent, discarding any earlier entry with other parent(s).
                        scores.insert(v, node_score + edge_weight);
                        visit_next.push(MinScored(node_score + edge_weight, v));
                        if let Some(v_pnode) = pathnodes.get(&v) {
                            let new_node: NodeData<G::NodeId, K> = NodeData {
                                node_id: v_pnode.node_id,
                                parent_id: Some(node),
                                cost: node_score + edge_weight,
                            };
                            pathnodes.insert(v_pnode.node_id, new_node);

                        } else {
                            assert_eq!(true, false, "Invariant not satisfied, Node {:?} not present in pathnodes", v);
                        }
                    }
                }
                Vacant(_) => {
                    // the node v has no entry in the priority queue so far.
                    // We must be visiting it the first time.
                    // Create the entry in the priority queue and an entry in the pathnodes map.
                    scores.insert(v, node_score + edge_weight);
                    visit_next.push(MinScored(node_score + edge_weight, v));
                    pathnodes.insert(v, NodeData {
                        node_id: v,
                        parent_id: Some(node),
                        cost: node_score + edge_weight
                    });
                }
            }
        }
    }

    // Now return the path
    let mut shortest_path: Vec<G::NodeId> = Vec::new();
    if let Some(target_node) = pathnodes.get(&target) {
        let min_cost = pathnodes.get(&target).unwrap().cost;

        // Let us just return one shortest path
        let mut current_node = target_node;
        shortest_path.push(current_node.node_id);
        while current_node.node_id != start {
            current_node = pathnodes.get(&current_node.parent_id.unwrap()).unwrap();
            shortest_path.push(current_node.node_id);
        }
        shortest_path.reverse();
        (shortest_path, min_cost)
    } else {
        (vec![], K::default())
    }
}



/// Implementation of Yen's Algorithm to find k shortest paths.
pub fn get_smallest_k_paths_yen<N, K, T>(
    graph: &mut Graph<N, K, T>,
    start: NodeIndex,
    target: NodeIndex,
    max_paths: usize,
) -> (Vec<Vec<NodeIndex>>)
where
    K: Measure + Copy,
    T: EdgeType,
{
    let mut listA: Vec < Vec <NodeIndex > > = Vec::new(); // list to contain shortest paths
    let (shortest_path, min_cost) = dijkstra_shortest_path_with_excluded_prefix(
        &*graph,
        start,
        target,
        |e| {*e.weight()},
        &HashSet::new());


    println!("Inserting path of cost {:?} in listA", min_cost);
    listA.push(shortest_path);
    // A binary heap that contains the candidate paths. In each iteration the candidate paths with
    // their costs are pushed on to the heap. The best path from the heap at the end of the iteration
    // is added to listA.
    let mut listB: BinaryHeap<MinScored<K, Vec<NodeIndex>>> = BinaryHeap::new();

    for i in 1usize..max_paths {
        // listA contains the i shortest paths, while listB contains candidate paths.
        // To determine the (i+1)^th shortest path we proceed as follows (according to Yen's algorithm)
        // We set the last added path in listA, i.e, the i^{th} shortest path as the current path.
        // Let x[0],...,x[ell-1] be the vertices in the current path.
        // We search for (i+1)^th path by considering paths which "diverge" from the current path at one
        // of the nodes x[0],...,x[ell-2]. However, we restrict these paths not to take diverging edge
        // which has appeared in any of the previous paths in listA, which are also identical to current
        // path till the node j. The new path is chosen as the minimum cost path from the following collection.
        // 1. Paths already in list B,
        // 2. The collection of shortest diverging paths from each of the nodes x[0],...x[ell-2].
        // A diverging path at x[j] is formed as union of current path till node x[j], and the shortest path
        // from x[j] to target after removing prohibited edges (see above).

        let mut current_path = listA[i-1].to_owned();                                   // current path is the last added path in listA
        let mut excluded_edges_map: HashMap<(NodeIndex, NodeIndex), K> = HashMap::new();                // map to keep track of removed edges, which are added back later
        let mut root_cost = K::default();                                                           // keep track of the cost of current path till diversion point.

        for j in 0usize..current_path.len() - 1 {
            // we are looking for diversion at current_path[j]
            let root_node = current_path[j];
            let next_edge = graph.find_edge(root_node, current_path[j+1]).unwrap();
            let next_edge_cost = *graph.edge_weight(next_edge).unwrap();

            for path in listA.iter() {
                // for each path that agrees with current path till node j,
                // remove the neighbor of j^{th} node on that path.
                if path.len() < j+1 {
                    continue;
                }

                if path[0..=j] == current_path[0..=j] {
                    if let Some(edge) = graph.find_edge(root_node, path[j+1]) {
                        excluded_edges_map.insert((root_node, path[j + 1]), *graph.edge_weight(edge).unwrap());
                        graph.remove_edge(edge);
                    }
                }
            }
            // find the shortest path form root_node to target in the graph after removing prohibited edges.
            let (shortest_root_target_path, path_cost) = dijkstra_shortest_path_with_excluded_prefix(
                &*graph,
                root_node,
                target,
                |e| {*e.weight()},
                &HashSet::from_iter(current_path[0..=j].to_vec().into_iter()),
            );

            if shortest_root_target_path.len() > 0 {
                // create new_path by appending current_path till divergence point and the shortest path after that.
                let mut new_path = current_path[0..j].to_owned();
                println!("new_path {:?}", new_path);
                new_path.extend_from_slice(&shortest_root_target_path);
                println!("Adding path of cost {:?} to listB", root_cost + path_cost);
                listB.push(MinScored(root_cost + path_cost, new_path));
            }

            // add current edge cost to the root cost
            root_cost = root_cost + next_edge_cost;
        };

        // finally restore the edges we removed to reset the graph for next iteration
        for (edge, wt) in &excluded_edges_map {
            graph.add_edge(edge.0, edge.1, *wt);
        }

        // remove the path of least cost from listB, and add to listA
        if let Some(MinScored(path_cost, min_path)) = listB.pop() {
            println!("Adding path of cost {:?} to listA", path_cost);
            listA.push(min_path);
        } else {
            // we have run out of candidates now.
            return listA;
        }
    }

    listA
}



/// To return next possible target for the path.
/// if all possible nodes are traced, then it picks the shortest endpoint and pick the nodes of next nodes.

fn get_smallest_k_element<P>(scores : & HashMap<NodeIndex,P> , visited : &mut Vec<NodeIndex>) -> 
Option<NodeIndex> where P: Copy + std::cmp::PartialOrd  + std::default::Default  + std::ops::Add<Output = P>  + std::fmt::Debug{
    if scores.len() == 1 {
        for (node,_score) in scores {
            return Some(node.clone());
        }
    }
    else {
        let mut score_vec: Vec<_> = scores.iter().collect();
        score_vec.sort_by(|&(_, &score1), &(_, &score2)| {
            score1.partial_cmp(&score2).unwrap_or(std::cmp::Ordering::Equal)
        });
        let mut count = 0;
        for (node,_score) in &score_vec {
            if ! visited.contains(node) {
                visited.push(**node);
                return Some(**node); 
            }  
            count = count + 1;
            if count == score_vec.len() {
                return Some(*score_vec[0].0);
            }
        }

    }
    return None;
}

/// public function to get all possible paths
/// The dijkastra returns values like -
///  (parent_node, node , total_score_to_reach_<node>_from_root_through_<parent_node>)
/// Using these values for each <node>  we extract and store a Hashmap of <parent_node ,score>.
/// then we backtrack from target till source to get the path. by picking one of the parent_nodes.
/// the last step is done for all possible paths.
/// For visiting all nodes of a parent_node, it only consider the shortest path of the <node> from <aprent_node> -> <node> .

pub fn get_shortest_paths<P,N,T>(graph: &mut Graph<T, P, N>,source: NodeIndex,target: NodeIndex, number_of_paths: Option<i32>) -> IntoIter<Option<Vec< NodeIndex>>>
where N: EdgeType,
P: Copy + std::cmp::PartialOrd  + std::default::Default  + std::ops::Add<Output = P>  + std::fmt::Debug {

    let mut final_paths : HashMap<NodeIndex, HashMap<NodeIndex, P>> = HashMap::new();
    let mut all_paths : HashMap<Vec<NodeIndex>, P> = HashMap::new();
    let mut visited : Vec<NodeIndex> = vec!();
    let mut shortest_paths : Vec<Option<Vec<NodeIndex>>>  = vec!();
    let mut paths : Vec<NodeIndex> = vec!();

    let (score_new, path) = dijkstra(&*graph,source, Some(target), |e| *e.weight());
    if ! score_new.contains_key(&target) {
        shortest_paths.push(None);
        return shortest_paths.into_iter();
    }

    for (node ,next,score) in path {
        if let Some(v) = final_paths.get_mut(&node) {
            v.insert(next,score);
        } else {
            final_paths.insert(node,HashMap::new());
            let Some(v) = final_paths.get_mut(&node)else { todo!() };
            v.insert(next, score);
        };
    }
    
    loop {
        paths.push(target);
        let mut node=target ;
        let mut total_score_path: P = P::default();
        loop { 
            let pre_node = get_smallest_k_element(&final_paths[&node] ,&mut visited);
            match pre_node {
            Some(s) => {
                paths.push(s);
                let edge = graph.find_edge(pre_node.expect("REASON"),node);
                let mut weight : P = P::default();
                match edge {
                    Some(edge) => {
                        weight = *graph.edge_weight(edge).unwrap();
                    },
                    None => {},

                };

                total_score_path = total_score_path + weight;
                if source == s { 
                    // If you have already reach to source from target, the path is complete.
                    break;
                }
                node = s;
                }
            None => {
                break;
            }
            }
            
        }
        paths.reverse();
        
        if all_paths.contains_key(&paths) {
            break;
        }
        all_paths.insert(paths,total_score_path);
        paths = vec!();
        total_score_path = P::default();
   }  
    
    let mut score_vec: Vec<_> = all_paths.iter().collect::<Vec<_>>().clone();
    score_vec.sort_by(|&(_, &score1), &(_, &score2)| {
        score1.partial_cmp(&score2).unwrap_or(std::cmp::Ordering::Equal)
    });

    let mut count = 0;
    let mut total_paths = 0;
    match number_of_paths {
        Some(K) => total_paths = K,
        None => total_paths = score_vec.len() as i32,

    }

    for (k,v ) in score_vec {
        // println!("Path {:#?} Score {:#?}",k,v);
        shortest_paths.push(Some(k.clone()));
        count = count +1;
        if count >= total_paths {
            break;
        }
    }

    return shortest_paths.into_iter();
}

///  Test Function
///  the graph can Directed or Undirected.
///  weight is must , pass 1 as weight for each edge if no weight is there for the graph.
///  It verifies all 2 paths generated for the graph.

#[cfg(test)]
mod tests {
    //use crate::get_shortest_paths;
    use petgraph::{Graph, Undirected};
    use petgraph::graph::NodeIndex;
    //use crate::shortest_path::get_shortest_paths;
    use crate::shortest_path::simple_shortest_paths::{dijkstra_k_shortest_paths, get_smallest_k_paths_yen};
    //use petgraph_evcxr::draw_graph;
    fn generate_n_cycle_example(n: usize) -> (Graph<usize, u32, Undirected>, Vec<NodeIndex>) {
        let mut g: Graph<usize, u32, Undirected> = Graph::new_undirected();
        let num_nodes = 6*n + 2;
        let mut node_names: Vec<usize> = Vec::new();
        for i in 0.. num_nodes {
            node_names.push(i);
        }
        let mut nodes = (0..num_nodes).into_iter().map(|i| g.add_node(node_names[i])).collect::<Vec<_>>();
        // build cycles
        for i in 0.. n {
            let base = 6 * i + 1;
            for j in 0..6 {
                g.add_edge(nodes[base + (j % 6)], nodes[base + ((j + 1) % 6)], (j+1) as u32);
            }
            g.add_edge(nodes[base + 3], nodes[base+6],1);
        }

        g.add_edge(nodes[0], nodes[1], 1);

        (g, nodes)
    }

    // Generates an undirected cycle of n edges, each with weight 1.
    fn generate_n_gon_example(n: usize) -> (Graph<usize, u32, Undirected>, Vec<NodeIndex>) {
        let mut g: Graph<usize, u32, Undirected> = Graph::new_undirected();
        let num_nodes = n;
        let mut node_names: Vec<usize> = Vec::new();
        for i in 0.. num_nodes {
            node_names.push(i);
        }
        let mut nodes = (0..num_nodes).into_iter().map(|i| g.add_node(node_names[i])).collect::<Vec<_>>();
        // build cycles
        for i in 0.. n {
            g.add_edge(nodes[i], nodes[(i+1) % n], 1);
        }
        (g, nodes)
    }

    fn generate_n_gon_with_chords_example(n: usize, step: usize) -> (Graph<usize, u32, Undirected>, Vec<NodeIndex>) {
        let mut g: Graph<usize, u32, Undirected> = Graph::new_undirected();
        let num_nodes = n;
        let mut node_names: Vec<usize> = Vec::new();
        for i in 0.. num_nodes {
            node_names.push(i);
        }
        let mut nodes = (0..num_nodes).into_iter().map(|i| g.add_node(node_names[i])).collect::<Vec<_>>();
        // build cycles
        for i in 0.. n {
            g.add_edge(nodes[i], nodes[(i+1) % n], 1);
            g.add_edge(nodes[i], nodes[(i+step) % n], 1);
        }
        (g, nodes)
    }


    #[test]
    fn test_k_shortest_paths() {
        let (mut graph, nodes) = generate_n_gon_with_chords_example(6, 2);

        let paths = get_smallest_k_paths_yen(
            &mut graph,
            nodes[0],
            nodes[1],
             5
        );

        for path in paths {
            println!("{:#?}", path);
        }




    }


    #[test]
    fn test_shortest_paths() {

        /*
        let mut g = Graph::new_undirected();
        let a = g.add_node("A");
        let b = g.add_node("B");
        let c = g.add_node("C");
        let d = g.add_node("D");
        let e = g.add_node("E");
        let f = g.add_node("F");
        g.add_edge(a, b, 7);
        g.add_edge(a, c, 9);
        g.add_edge(a, d, 14);
        g.add_edge(b, c, 10);
        g.add_edge(d, c, 2);
        g.add_edge(d, e, 9);
        g.add_edge(b, f, 15);
        g.add_edge(c, f, 11);
        g.add_edge(e, f, 6);
      let source = a;
      let target = f;
      let mut path1 = [
        a,
        c,
        f,
      ];

      let path2 = [
        a,
        b,
        f,
       ];

      // You should pass None for parameter number_of_paths if you want all possible shortest
        let (mut g, nodes) = generate_n_cycle_example(10);
        let paths = get_shortest_paths(&mut g, nodes[0], nodes[61], None);
        println!("Total paths = {}", paths.len());
        for path in paths {
        println!("{:?}",path);

       match path {
        Some(p) => assert_eq!(p, path1),
        None => panic!("Not matched"),
        }
        path1 = path2;

           */
      }

}


