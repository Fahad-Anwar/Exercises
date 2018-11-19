package analysis.exercise3;

import java.util.ArrayList;
import java.util.List;

import soot.RefType;
import soot.Value;

public class TypeGraph {
	List<Node> nodeList;
	List<Edge> edgeList;

	public TypeGraph() {
		this.nodeList = new ArrayList<Node>();
		this.edgeList = new ArrayList<Edge>();
	}

	public List<RefType> getAllTypes() {
		List<RefType> l = new ArrayList<RefType>();
		for (Node n : this.nodeList) {
			for (RefType t : n.t) {
				l.add(t);
			}
		}
		return l;
	}

	public void printMe() {
		this.nodeList.forEach(n -> {
			System.out.println("node: " + n.v);
			n.t.forEach(t -> {
				System.out.println("type: " + t);
			});
			System.out.println();
		});

		this.edgeList.forEach(e -> {
			System.out.println("edge");
			e.printMe();
		});
	}

	public void addNode(Value v) {
		if (!this.containsNode(v))
			nodeList.add(new Node(v));
	}

	private boolean containsNode(Value v) {

		for (Node n : this.nodeList) {
			if (n.hasValue(v)) {
				return true;
			}
		}
		return false;
	}

	public void addTypeToNode(RefType t, Value v) {
		this.nodeList.forEach(n -> {
			if (n.hasValue(v)) {
				n.addType(t);
			}
		});
	}

	private class Node {
		private Value v;
		private List<RefType> t;

		public Node(Value v) {
			this.v = v;
			this.t = new ArrayList<RefType>();
		}

		public boolean hasValue(Value v) {
			return v.equivTo(this.v);
		}

		public void addType(RefType t) {
			this.t.add(t);
		}
	}

	private class Edge {
		Node from, to;

		public Edge(Node from, Node to) {
			this.from = from;
			this.to = to;
		}

		public void printMe() {
			System.out.println("edge from: " + from.v + " to: " + to.v);
		}
	}

	private Node getNodeForValue(Value v) {
		for (Node n : this.nodeList) {
			if (n.hasValue(v)) {
				return n;
			}
		}
		return null;
	}

	public void addEdge(Value leftOp, Value rightOp) {
		Node l = this.getNodeForValue(leftOp);
		Node r = this.getNodeForValue(rightOp);
		if (l != null && r != null)
			this.edgeList.add(new Edge(l, r));

	}
}