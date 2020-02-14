package edu.harvard.seas.pl.formulog.db;

/*-
 * #%L
 * FormuLog
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

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import java.util.function.BiFunction;

import org.jgrapht.Graph;
import org.jgrapht.graph.SimpleDirectedGraph;

import edu.harvard.seas.pl.formulog.util.Util;

public class MinChainCover<T> {

	private final BiFunction<T, T, Boolean> lessThan;
	
	public MinChainCover(BiFunction<T, T, Boolean> lessThan) {
		this.lessThan = lessThan;
	}
	
	public Iterable<Iterable<T>> compute(Set<T> elts) {
		return new Worker(elts).go();
	}

	private class Worker {

		private final BiGraphNode source = new BiGraphNode() {
			
			@Override
			public String toString() {
				return "source";
			}
			
		};
		private final BiGraphNode sink = new BiGraphNode() {
			
			@Override
			public String toString() {
				return "sink";
			}
			
		};
		private final Graph<BiGraphNode, BiGraphEdge> bigraph = new SimpleDirectedGraph<>(BiGraphEdge.class);
		private final T[] elts;
		private final Boolean[][] memo;

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
				BiGraphNode left = new FilledBiGraphNode(elt, false);
				BiGraphNode right = new FilledBiGraphNode(elt, true);
				bigraph.addVertex(left);
				bigraph.addVertex(right);
				bigraph.addEdge(source, left, new BiGraphEdge(source, left));
				bigraph.addEdge(right, sink, new BiGraphEdge(right, sink));
			}
			for (int i = 0; i < elts.length; ++i) {
				BiGraphNode iv = new FilledBiGraphNode(elts[i], false);
				for (int j = 0; j < elts.length; ++j) {
					considerEdge(i, iv, j);
				}
			}
			Util.printGraph(System.out, bigraph);
		}

		private void considerEdge(int i, BiGraphNode iv, int j) {
			if (memo[i][j] == null) {
				memoize(i, j);
			}
			if (memo[i][j]) {
				BiGraphNode jv = new FilledBiGraphNode(elts[j], true);
				bigraph.addEdge(iv, jv, new BiGraphEdge(iv, jv));
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

		private Iterable<Iterable<T>> mkChains() {
			return null;
		}
		
	}

	private static interface BiGraphNode {

	}

	private class FilledBiGraphNode implements BiGraphNode {

		public final T elt;
		public final boolean side;

		public FilledBiGraphNode(T elt, boolean side) {
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
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			@SuppressWarnings("unchecked")
			FilledBiGraphNode other = (FilledBiGraphNode) obj;
			if (elt == null) {
				if (other.elt != null)
					return false;
			} else if (!elt.equals(other.elt))
				return false;
			if (side != other.side)
				return false;
			return true;
		}
		
		@Override
		public String toString() {
			return elt + ((side) ? "@R" : "@L");
		}

	}

	private static class BiGraphEdge {

		public final BiGraphNode src;
		public final BiGraphNode dst;

		public BiGraphEdge(BiGraphNode src, BiGraphNode dst) {
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
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			BiGraphEdge other = (BiGraphEdge) obj;
			if (dst == null) {
				if (other.dst != null)
					return false;
			} else if (!dst.equals(other.dst))
				return false;
			if (src == null) {
				if (other.src != null)
					return false;
			} else if (!src.equals(other.src))
				return false;
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
		mcc.compute(elts);
	}

}