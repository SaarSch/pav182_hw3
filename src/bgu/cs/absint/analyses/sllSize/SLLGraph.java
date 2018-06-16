package bgu.cs.absint.analyses.sllSize;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;

import bgu.cs.absint.analyses.zone.ZoneDomain;
import bgu.cs.absint.analyses.zone.ZoneFactoid;
import bgu.cs.absint.analyses.zone.ZoneState;
import bgu.cs.absint.soot.LocalComparator;
import bgu.cs.util.StringUtils;
import soot.Local;
import soot.jimple.IntConstant;

/**
 * An abstract element representing the abstraction of a bounded number of
 * interacting singly-linked lists (bounded by the number of local
 * variables).<br>
 * Each list segment is associated with a numeric variable that represents its
 * size and the numeric relations between these variables is represented by an
 * element of the Zone domain.
 * 
 * @author romanm
 */
public class SLLGraph {
	public final Node nullNode = new Node(null);

	protected Collection<Node> nodes = new ArrayList<Node>();
	protected Map<Local, Node> pointsTo = new TreeMap<Local, Node>(new LocalComparator());

	/**
	 * Maintains numeric relations between all list segments.
	 */
	protected ZoneState sizes;

	public SLLGraph() {
		nodes.add(nullNode);
		sizes = new ZoneState();
	}

	public SLLGraph dropLocals(Collection<Local> locals) {
		SLLGraph simpler = this.copy();
		for (Local local : locals) {
			simpler.pointsTo.remove(local);
			// TODO: sizes.removeVar(local); ?
		}
		return simpler;
	}

	/**
	 * Creates an isomorphic shape graph.
	 * 
	 * @return A shape graph that is isomorphic to this one.
	 */
	public SLLGraph copy() {
		SLLGraph result = new SLLGraph();
		// Matches a node in this graph to a node in the result graph.
		Map<Node, Node> matching = new HashMap<>(nodes.size());
		for (Node node : nodes) {
			if (node == nullNode)
				continue;
			Node newNode = new Node();
			newNode.pointedBy = new HashSet<>(node.pointedBy);
			matching.put(node, newNode);
			result.addNode(newNode);
		}
		// Match the null node separately.
		matching.put(nullNode, result.nullNode);

		// Now update the next pointers.
		for (Map.Entry<Node, Node> entry : matching.entrySet()) {
			Node thisNode = entry.getKey();
			Node otherNode = entry.getValue();
			if (thisNode.next != null) {
				otherNode.next = matching.get(thisNode.next);
			}
			otherNode.edgeLen = thisNode.edgeLen;
		}

		// Finally, update the pointsTo map.
		for (Map.Entry<Local, Node> entry : pointsTo.entrySet()) {
			Local var = entry.getKey();
			Node node = entry.getValue();
			Node otherNode = matching.get(node);
			result.pointsTo.put(var, otherNode);
		}

		result.sizes = sizes.copy();

		return result;
	}

	public Collection<Node> getNodes() {
		return nodes;
	}

	public Set<Node> getPreds(Node n) {
		HashSet<Node> result = new HashSet<>();
		for (Node p : getNodes()) {
			if (p.next == n)
				result.add(p);
		}
		return result;
	}

	public Node pointsTo(Local v) {
		return pointsTo.get(v);
	}

	public void addNode(Node n) {
		assert !nodes.contains(n);
		if (n.next != null)
			assert nodes.contains(n.next) : "Attempt to add a node where the next node is not part of the same graph!";
			nodes.add(n);
	}

	public void removeNode(Node n) {
		assert n != nullNode;
		nodes.remove(n);
		sizes.removeVar(n.edgeLen);
	}

	public void mapLocal(Local v, Node n) {
		assert nodes.contains(n);
		unmapLocal(v);
		n.addLocal(v);
		pointsTo.put(v, n);
	}

	public void unmapLocal(Local v) {
		Node n = pointsTo(v);
		if (n != null) {
			n.removeLocal(v);
			pointsTo.remove(v);
		}
	}

	public void removeGarbageNodes() {
		HashSet<Node> reachable = new HashSet<>(pointsTo.values());
		HashSet<Node> workset = new HashSet<>(pointsTo.values());
		while (!workset.isEmpty()) {
			Node n = workset.iterator().next();
			workset.remove(n);
			Node next = n.next;
			if (next != null && !reachable.contains(next)) {
				reachable.add(next);
				workset.add(next);
			}
		}
		//TODO: remove locals from ZoneState?
		nodes.retainAll(reachable);
	}

	public void addSizeFactoid(Node n, int edgeLenBound, boolean invertFactoid)
	{
		if (invertFactoid)
			sizes.addFactoid(ZoneFactoid.ZERO_VAR, n.edgeLen, IntConstant.v(-edgeLenBound)); // add the Factoid: -x<=-edgeLenBound === x>=edgeLenBound
		else
			sizes.addFactoid(n.edgeLen, ZoneFactoid.ZERO_VAR, IntConstant.v(edgeLenBound)); // add the Factoid: x<=edgeLenBound

		//sizes = ZoneDomain.v().reduce(sizes);
	}

	public void addSizeFactoid(Node n, int edgeLenBound)
	{
		addSizeFactoid(n, edgeLenBound, false);
	}

	public void addSizeEqualsFactoids(Node n, int edgeLenBound)
	{
		addSizeFactoid(n, edgeLenBound, false); // edgeLen<=bound
		addSizeFactoid(n, edgeLenBound, true); // edgeLen>=bound
	}

	public boolean checkIfEdgeLenEquals(Node n, int len)
	{
		boolean res = false;
		if (sizes == ZoneDomain.v().getBottom() ||
				sizes == ZoneDomain.v().getTop())
			return res;
		ZoneFactoid f1 = new ZoneFactoid(n.edgeLen, ZoneFactoid.ZERO_VAR, IntConstant.v(len));
		ZoneFactoid f2 = new ZoneFactoid(ZoneFactoid.ZERO_VAR, n.edgeLen, IntConstant.v(-len));
		for (ZoneFactoid f : sizes.getFactoids())
		{
			if (f.eq(f1) || f.eq(f2))
			{
				if (res)
					return true;
				res = true;
			}
		}
		return false;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + nodes.size();
		for (Node n : pointsTo.values()) {
			result = prime * result + n.pointedBy.hashCode();
		}
		result = prime * result + sizes.hashCode();
		return result;
	}

	/**
	 * Checks whether this graph is isomorphic to the given one.
	 */
	@Override
	public boolean equals(Object o) {
		SLLGraph other = (SLLGraph) o;

		if (nodes.size() != other.nodes.size())
			return false;

		// Attempt to create an initial matching of nodes based on
		// the pointed-by sets.
		Map<Node, Node> matching = new HashMap<>();
		for (Map.Entry<Local, Node> entry : pointsTo.entrySet()) {
			Local v = entry.getKey();
			Node n = entry.getValue();
			assert n != null;
			Node otherNode = other.pointsTo(v);
			if (otherNode == null)
				return false;
			if (!n.pointedBy.equals(otherNode.pointedBy))
				return false;
			matching.put(n, otherNode);
		}

		// Complete the matching based on the 'next' relation.
		HashSet<Node> workset = new HashSet<>();
		workset.addAll(matching.keySet());
		while (!workset.isEmpty()) {
			Node nodeToCheck = workset.iterator().next();
			workset.remove(nodeToCheck);
			Node matchedNodeToCheck = matching.get(nodeToCheck);
			assert matchedNodeToCheck != null;
			Node nextNode = nodeToCheck.next;
			if (nextNode != null) {
				matching.put(nextNode, matchedNodeToCheck.next);
				if (!matching.containsKey(nextNode)) {
					workset.add(nextNode);
				}
			}
		}

		// Finally, check that the matching preserves the 'next' relation.
		for (Map.Entry<Node, Node> entry : matching.entrySet()) {
			Node thisNode = entry.getKey();
			Node otherNode = entry.getValue();
			if (thisNode.edgeLen != otherNode.edgeLen)
				return false;
			if (thisNode.next == null) {
				if (otherNode.next != null)
					return false;
			} else {
				Node matchedNextNode = matching.get(thisNode.next);
				if (matchedNextNode == null)
					return false;
				if (matchedNextNode != otherNode.next)
					return false;
			}
		}

		return true;
	}

	// Iterate over the graph in DFS, pointing the edgeLen Local of each node we encounter to the next Local
	public void normalize() {
		SLLDomain.v().clearAllocatedLens(); // start allocating len locals from 0
		Set<Node> visited = new HashSet<>();
		SortedSet<Local> sortedLocals = new TreeSet<Local>(
				new Comparator<Local>() {
					@Override
					public int compare(Local l1, Local l2) {
						return l1.getName().compareTo(l2.getName());
					}
				});
		sortedLocals.addAll(pointsTo.keySet()); // sorted

		Map<Local, Local> changes = new HashMap<>();
		Iterator<Local> iter = sortedLocals.iterator();
		while (iter.hasNext())
		{
			Local local = iter.next();
			Node n = pointsTo(local);
			while (/*n != nullNode &&*/ n != null && !visited.contains(n))
			{
				Local lenLocal = SLLDomain.v().getLenLocal();
				if (sizes.getFactoids() != null) {
					for (ZoneFactoid f : sizes.getFactoids())
					{
						if (f.lhs == n.edgeLen)
							changes.put(f.lhs, lenLocal);
						else if (f.rhs == n.edgeLen)
							changes.put(f.rhs, lenLocal);
					}			
				}		

				n.edgeLen = lenLocal;
				visited.add(n);
				n = n.next;
			}
		}

		List<ZoneFactoid> newFactoids = new ArrayList<>();
		if (sizes.getFactoids() != null) {
			for (ZoneFactoid f : sizes.getFactoids())
			{
				if (changes.containsKey(f.lhs) && changes.containsKey(f.rhs))
					newFactoids.add(new ZoneFactoid(changes.get(f.lhs), changes.get(f.rhs), f.bound));
				else if (changes.containsKey(f.lhs))
					newFactoids.add(new ZoneFactoid(changes.get(f.lhs), f.rhs, f.bound));
				else if (changes.containsKey(f.rhs))
					newFactoids.add(new ZoneFactoid(f.lhs, changes.get(f.rhs), f.bound));
				else
					newFactoids.add(new ZoneFactoid(f.lhs, f.rhs, f.bound));
			}
		}

		ZoneState newState = new ZoneState();
		for (ZoneFactoid f : newFactoids)
			newState.add(f);
		sizes = newState;
	}

	@Override
	public String toString() {
		ArrayList<String> substrings = new ArrayList<>();
		Map<Node, String> nodeToName = new HashMap<>();
		int i = 0;
		for (Node n : nodes) {
			if (n == nullNode) // Name the null node separately.
				continue;
			nodeToName.put(n, "n" + i);
			++i;
		}
		nodeToName.put(nullNode, "null");

		for (Map.Entry<Local, Node> entry : pointsTo.entrySet()) {
			Local v = entry.getKey();
			Node n = entry.getValue();
			substrings.add(v + "=" + nodeToName.get(n));
		}
		for (Node n : nodes) {
			if (n == nullNode) // Skip null node.
				continue;
			assert n.next != null;
			String nextNodeName = nodeToName.get(n.next);
			String edgeLenStr = checkIfEdgeLenEquals(n, 1) ? ".next=" : "~>";
			substrings.add(nodeToName.get(n) + edgeLenStr + nextNodeName);
		}
		substrings.add("ZoneState: [" + sizes.toString() + "]");
		StringBuilder result = new StringBuilder("graph = {");
		result.append(StringUtils.toString(substrings));
		result.append("}");
		return result.toString();
	}

	public int getEdgeLenBound(Node n) {
		Collection<ZoneFactoid> factoids = sizes.getFactoids();
		for (ZoneFactoid factoid : factoids)
		{
			Local var = n.edgeLen;
			if (factoid.hasVar(var))
			{
				if (factoid.rhs == ZoneFactoid.ZERO_VAR // x <= c
						|| factoid.lhs == ZoneFactoid.ZERO_VAR) // -x <= -c
					return factoid.bound.value;
			}
		}
		return -1; // error value
	}
}