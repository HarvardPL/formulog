package edu.harvard.seas.pl.formulog.db;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2020 President and Fellows of Harvard College
 * %%
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 * #L%
 */

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;
import org.jgrapht.Graph;
import org.jgrapht.alg.flow.PushRelabelMFImpl;
import org.jgrapht.alg.interfaces.MaximumFlowAlgorithm;
import org.jgrapht.graph.SimpleDirectedGraph;

public class MinChainCover<T> {

  private final BiFunction<T, T, Boolean> lessThan;

  public MinChainCover(BiFunction<T, T, Boolean> lessThan) {
    this.lessThan = lessThan;
  }

  public Iterable<Iterable<T>> compute(Set<T> elts) {
    return new Worker(elts).go();
  }

  private class Worker {

    private final Graph<Node, Edge> bigraph = new SimpleDirectedGraph<>(Edge.class);
    private final T[] elts;
    private final Boolean[][] memo;

    private final Node source =
        new Node() {

          @Override
          public String toString() {
            return "source";
          }
        };

    private final Node sink =
        new Node() {

          @Override
          public String toString() {
            return "sink";
          }
        };

    @SuppressWarnings("unchecked")
    public Worker(Set<T> s) {
      int n = s.size();
      elts = (T[]) new Object[n];
      int i = 0;
      for (T elt : s) {
        elts[i] = elt;
        ++i;
      }
      memo = new Boolean[n][n];
    }

    public Iterable<Iterable<T>> go() {
      mkBipartiteGraph();
      return mkChains();
    }

    private void mkBipartiteGraph() {
      bigraph.addVertex(source);
      bigraph.addVertex(sink);
      for (T elt : elts) {
        Node left = new InnerNode(elt, false);
        Node right = new InnerNode(elt, true);
        bigraph.addVertex(left);
        bigraph.addVertex(right);
        bigraph.addEdge(source, left, new Edge(source, left));
        bigraph.addEdge(right, sink, new Edge(right, sink));
      }
      for (int i = 0; i < elts.length; ++i) {
        Node iv = new InnerNode(elts[i], false);
        for (int j = 0; j < elts.length; ++j) {
          considerEdge(i, iv, j);
        }
      }
    }

    private void considerEdge(int i, Node iv, int j) {
      if (memo[i][j] == null) {
        memoize(i, j);
      }
      if (memo[i][j]) {
        Node jv = new InnerNode(elts[j], true);
        bigraph.addEdge(iv, jv, new Edge(iv, jv));
      }
    }

    private void memoize(int i, int j) {
      if (i == j) {
        memo[i][j] = false;
        return;
      }
      if (lessThan.apply(elts[i], elts[j])) {
        memo[i][j] = true;
        for (int k = 0; k < elts.length; ++k) {
          Boolean b = memo[j][k];
          if (b != null && b) {
            memo[i][k] = true;
          }
        }
      } else {
        memo[i][j] = false;
      }
    }

    private Map<Edge, Double> computeMaxFlowMap() {
      MaximumFlowAlgorithm<Node, Edge> maxFlow = new PushRelabelMFImpl<>(bigraph);
      return maxFlow.getMaximumFlow(source, sink).getFlowMap();
    }

    @SuppressWarnings("unchecked")
    private Iterable<Iterable<T>> mkChains() {
      Map<Edge, Double> maxFlowMap = computeMaxFlowMap();
      Set<T> roots = new HashSet<>(Arrays.asList(elts));
      Map<T, T> m = new HashMap<>();
      for (Map.Entry<Edge, Double> entry : maxFlowMap.entrySet()) {
        if (entry.getValue() > 0) {
          Edge edge = entry.getKey();
          if (edge.src == source || edge.dst == sink) {
            continue;
          }
          InnerNode src = (InnerNode) edge.src;
          InnerNode dst = (InnerNode) edge.dst;
          roots.remove(dst.elt);
          T other = m.put(src.elt, dst.elt);
          assert other == null;
        }
      }
      List<Iterable<T>> chains = new ArrayList<>();
      for (T root : roots) {
        T cur = root;
        List<T> chain = new ArrayList<>();
        while (cur != null) {
          chain.add(cur);
          cur = m.get(cur);
        }
        chains.add(chain);
      }
      return chains;
    }
  }

  private static interface Node {}

  private class InnerNode implements Node {

    public final T elt;
    public final boolean side;

    public InnerNode(T elt, boolean side) {
      this.elt = elt;
      this.side = side;
    }

    @Override
    public int hashCode() {
      final int prime = 31;
      int result = 1;
      result = prime * result + ((elt == null) ? 0 : elt.hashCode());
      result = prime * result + (side ? 1231 : 1237);
      return result;
    }

    @Override
    public boolean equals(Object obj) {
      if (this == obj) return true;
      if (obj == null) return false;
      if (getClass() != obj.getClass()) return false;
      @SuppressWarnings("unchecked")
      InnerNode other = (InnerNode) obj;
      if (elt == null) {
        if (other.elt != null) return false;
      } else if (!elt.equals(other.elt)) return false;
      if (side != other.side) return false;
      return true;
    }

    @Override
    public String toString() {
      return elt + ((side) ? "@R" : "@L");
    }
  }

  private static class Edge {

    public final Node src;
    public final Node dst;

    public Edge(Node src, Node dst) {
      this.src = src;
      this.dst = dst;
    }

    @Override
    public int hashCode() {
      final int prime = 31;
      int result = 1;
      result = prime * result + ((dst == null) ? 0 : dst.hashCode());
      result = prime * result + ((src == null) ? 0 : src.hashCode());
      return result;
    }

    @Override
    public boolean equals(Object obj) {
      if (this == obj) return true;
      if (obj == null) return false;
      if (getClass() != obj.getClass()) return false;
      Edge other = (Edge) obj;
      if (dst == null) {
        if (other.dst != null) return false;
      } else if (!dst.equals(other.dst)) return false;
      if (src == null) {
        if (other.src != null) return false;
      } else if (!src.equals(other.src)) return false;
      return true;
    }

    @Override
    public String toString() {
      return src + " ---> " + dst;
    }
  }

  public static void main(String[] args) {
    Set<String> s1 = new HashSet<>(Arrays.asList("x"));
    Set<String> s2 = new HashSet<>(Arrays.asList("x", "y"));
    Set<String> s3 = new HashSet<>(Arrays.asList("x", "z"));
    Set<String> s4 = new HashSet<>(Arrays.asList("x", "y", "z"));
    Set<Set<String>> elts = new HashSet<>(Arrays.asList(s1, s2, s3, s4));
    MinChainCover<Set<String>> mcc = new MinChainCover<>((x, y) -> y.containsAll(x));
    System.out.println(mcc.compute(elts));
  }
}
