package bgu.cs.absint.analyses.sllSize;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import soot.IntType;
import soot.Local;
import soot.RefType;
import soot.SootField;
import soot.Type;
import soot.Unit;
import soot.jimple.AssignStmt;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.StringConstant;
import soot.jimple.internal.JimpleLocal;
import bgu.cs.absint.AssumeTransformer;
import bgu.cs.absint.ComposedOperation;
import bgu.cs.absint.ErrorState;
import bgu.cs.absint.AbstractDomain;
import bgu.cs.absint.IdOperation;
import bgu.cs.absint.UnaryOperation;
import bgu.cs.absint.analyses.zone.ZoneDomain;
import bgu.cs.absint.analyses.zone.ZoneFactoid;
import bgu.cs.absint.analyses.zone.ZoneState;
import bgu.cs.absint.constructor.DisjunctiveState;
import bgu.cs.absint.soot.TransformerMatcher;

/**
 * An abstract domain for the intraprocedural shape analysis of singly-linked
 * lists.
 * 
 * @author romanm
 */
public class SLLDomain extends AbstractDomain<DisjunctiveState<SLLGraph>, Unit> {
	/**
	 * Singleton value.
	 */
	private static final SLLDomain v = new SLLDomain();
	private List<Local> lenLocals = new ArrayList<Local>();
	private int currentLenVariable = 0;

	public static final SLLDomain v() {
		return v;
	}

	protected DisjunctiveState<SLLGraph> bottom;
	protected DisjunctiveState<SLLGraph> top;

	/**
	 * The set of local variables in the current method body.
	 */
	protected Set<Local> locals;

	/**
	 * A helper object that matches statements to transformers.
	 */
	protected SLLMatcher matcher = new SLLMatcher();

	/**
	 * The name of the list class.
	 */
	private String listClassName;

	/**
	 * The name of the next field of the list class.
	 */
	private String listClassField;

	public void setBodyLocals(Collection<Local> locals) {
		this.locals = new LinkedHashSet<>(locals);
		lenLocals.clear();
		currentLenVariable = 0;
		for (int i = 0; i < locals.size() * 2 + 1; i++)
			lenLocals.add(new JimpleLocal("len" + i, IntType.v()));
	}

	public void setListClass(String listClassName, String listClassField) {
		this.listClassName = listClassName;
		this.listClassField = listClassField;
	}

	public void decrementAllocatedLens() {
		currentLenVariable--;
	}

	public void clearAllocatedLens() {
		currentLenVariable = 0;
	}

	@Override
	public DisjunctiveState<SLLGraph> getBottom() {
		return bottom;
	}

	@Override
	public DisjunctiveState<SLLGraph> getTop() {
		return top;
	}

	/**
	 * Returns the set union of both input sets.
	 */
	@Override
	public DisjunctiveState<SLLGraph> ub(DisjunctiveState<SLLGraph> elem1, DisjunctiveState<SLLGraph> elem2) {
		// Special treatment for top.
		if (elem1 == getTop() || elem2 == getTop())
			return getTop();

		Set<SLLGraph> disjuncts = new HashSet<SLLGraph>();

		Iterator<SLLGraph> iter1 = elem1.iterator();
		Iterator<SLLGraph> iter2 = elem2.iterator();

		while (iter1.hasNext()) {
			SLLGraph curr1 = iter1.next();
			while (iter2.hasNext()) {
				SLLGraph curr2 = iter2.next();
				if (curr1.equals(curr2)) // graphs are isomorphic
				{
					ZoneState joinedState = ZoneDomain.v().ub(curr1.sizes, curr2.sizes);
					SLLGraph res = curr1.copy();
					res.sizes = joinedState;
					disjuncts.add(res);
				}
				else {
					disjuncts.add(curr1);
					disjuncts.add(curr2);
				}
			}
			iter2 = elem2.iterator();
		}

		DisjunctiveState<SLLGraph> result = new DisjunctiveState<SLLGraph>(disjuncts);
		return result;
	}

	/**
	 * Applies {@code generalize} to the shape graphs in both input sets.
	 */
	@Override
	public DisjunctiveState<SLLGraph> ubLoop(DisjunctiveState<SLLGraph> elem1, DisjunctiveState<SLLGraph> elem2) {
		// Special treatment for top.
		if (elem1 == getTop() || elem2 == getTop())
			return getTop();

		HashSet<SLLGraph> disjuncts = new HashSet<>();
		for (SLLGraph graph : elem1) {
			SLLGraph disjunct = generalize(graph);
			disjuncts.add(disjunct);
		}
		for (SLLGraph graph : elem2) {
			SLLGraph disjunct = generalize(graph);
			disjuncts.add(disjunct);
		}

		DisjunctiveState<SLLGraph> result = new DisjunctiveState<SLLGraph>(disjuncts);
		return result;
	}

	@Override
	public boolean leq(DisjunctiveState<SLLGraph> first, DisjunctiveState<SLLGraph> second) {
		// Special treatment for top.
		if (second == getTop())
			return true;
		else if (first == getTop())
			return false;
		else
			return second.getDisjuncts().containsAll(first.getDisjuncts());
	}

	@Override
	public DisjunctiveState<SLLGraph> widen(DisjunctiveState<SLLGraph> first, DisjunctiveState<SLLGraph> second) {
		// Special treatment for top.
		if (first == getTop() || second == getTop())
			return getTop();

		Set<SLLGraph> disjuncts = new HashSet<SLLGraph>();
		
		disjuncts.addAll(first.getDisjuncts());

		
		for (SLLGraph curr : second.getDisjuncts()) {
			SLLGraph res = curr.copy();
			SLLGraph isomorphic;
			if ((isomorphic = getIsomorphicGraph(curr, first.getDisjuncts())) != null) {
				ZoneState widenedState = ZoneDomain.v().widen(isomorphic.sizes, curr.sizes);
				res.sizes = widenedState;
			}
			disjuncts.add(res);
		}

		return new DisjunctiveState<SLLGraph>(disjuncts);
	}

	@Override
	public DisjunctiveState<SLLGraph> narrow(DisjunctiveState<SLLGraph> first, DisjunctiveState<SLLGraph> second) {
		// Special treatment for bottom.
		if (second == getBottom())
			return first;

		Set<SLLGraph> disjuncts = new HashSet<SLLGraph>();
		
		disjuncts.addAll(first.getDisjuncts());

		
		for (SLLGraph curr : second.getDisjuncts()) {
			SLLGraph res = curr.copy();
			SLLGraph isomorphic;
			if ((isomorphic = getIsomorphicGraph(curr, first.getDisjuncts())) != null) {
				ZoneState narrowedState = ZoneDomain.v().narrow(isomorphic.sizes, curr.sizes);
				res.sizes = narrowedState;
			}
			disjuncts.add(res);
		}

		return new DisjunctiveState<SLLGraph>(disjuncts);
	}
	
	private SLLGraph getIsomorphicGraph(SLLGraph g, Set<SLLGraph> set) {
		for (SLLGraph other : set)
			if (g.equals(other))
				return other;
		return null;
	}

	@Override
	public UnaryOperation<DisjunctiveState<SLLGraph>> getTransformer(Unit stmt) {
		UnaryOperation<DisjunctiveState<SLLGraph>> vanillaTransformer = matcher.getTransformer(stmt);
		if (vanillaTransformer.equals(IdOperation.v())) {
			// An optimization - no need to run a reduction after an identity
			// transformer.
			return vanillaTransformer;
		} else {
			return ComposedOperation.compose(vanillaTransformer, getReductionOperation());
		}
	}

	/**
	 * A reduction operator. The operator reduces the ZoneState of each SLLGraph in
	 * the DisjunctiveState
	 */
	@Override
	public DisjunctiveState<SLLGraph> reduce(DisjunctiveState<SLLGraph> input) {
		if (isErrorState(input))
			return input;
		// Special treatment for bottom & top.
		if (input == getBottom())
			return input;
		if (input == getTop())
			return getTop();

		DisjunctiveState<SLLGraph> result = copyDisjunctiveState(input);
		Iterator<SLLGraph> iter = result.iterator();
		while (iter.hasNext()) {
			SLLGraph curr = iter.next();
			curr.sizes = ZoneDomain.v().reduce(curr.sizes);
		}
		return result;
	}

	private boolean isErrorState(DisjunctiveState<SLLGraph> input) {
		if (input instanceof AssertLengthDiff.IncorrectLengthDiffState ||
			input instanceof AssertNoGarbageTransformer.GarbageExistsState ||
			input instanceof AssertAcyclicTransformer.NotAcyclicState ||
			input instanceof AssertCyclicTransformer.NotCyclicState ||
			input instanceof AssertReachableTransformer.NotReachableState ||
			input instanceof AssertDisjointTransformer.NotDisjointState)
			return true;
		return false;
	}

	private DisjunctiveState<SLLGraph> copyDisjunctiveState(DisjunctiveState<SLLGraph> input) {
		Set<SLLGraph> res = new HashSet<>();
		Iterator<SLLGraph> iter = input.iterator();
		while (iter.hasNext())
			res.add(iter.next().copy());
		return new DisjunctiveState<>(res);
	}

	// ////////////////////////////////////////////////////////////////////////////
	// Utility methods for singly-linked list shape graphs.
	// ////////////////////////////////////////////////////////////////////////////

	/**
	 * Checks whether a given local variable has the type specified as the list
	 * class type.
	 */
	public boolean isListRefType(Local var) {
		Type varType = var.getType();
		if (varType instanceof RefType) {
			RefType refType = (RefType) varType;
			if (refType.getClassName().equals(listClassName))
				return true;
			else
				return false;
		} else {
			return false;
		}
	}

	/**
	 * Creates a shape graph where all list variables point to null.
	 */
	public SLLGraph makeAllNullsGraph() {
		SLLGraph allNullsGraph = new SLLGraph();
		for (Local var : locals) {
			if (isListRefType(var))
				allNullsGraph.mapLocal(var, allNullsGraph.nullNode);
		}
		return allNullsGraph;
	}

	/**
	 * Creates a state containing a shape graph where all list variables point to
	 * null.
	 */
	public DisjunctiveState<SLLGraph> initNulls() {
		DisjunctiveState<SLLGraph> result = new DisjunctiveState<>(makeAllNullsGraph());
		return result;
	}

	/**
	 * Creates state containing two shape graphs where all list variables point to
	 * null, except a given list variable, which points to an acyclic list of size
	 * >= 0.
	 */
	public DisjunctiveState<SLLGraph> initAcyclic(Local x) {
		SLLGraph graph1 = makeAllNullsGraph();
		Node ptXOne = new Node(graph1.nullNode);
		graph1.addNode(ptXOne);
		graph1.mapLocal(x, ptXOne);
		graph1.normalize();
		graph1.addSizeEqualsFactoids(ptXOne, 1);

		SLLGraph graph2 = makeAllNullsGraph();
		Node ptXGt1 = new Node(graph2.nullNode);
		graph2.addNode(ptXGt1);
		graph2.mapLocal(x, ptXGt1);
		graph2.normalize();
		graph2.addSizeFactoid(ptXGt1, 2, true);

		SLLGraph allNulls = makeAllNullsGraph();
		allNulls.normalize();

		DisjunctiveState<SLLGraph> result = new DisjunctiveState<>(allNulls, graph1, graph2);
		return result;
	}

	public Local getLenLocal() {
		if (currentLenVariable >= lenLocals.size())
			return null;
		Local lenLocal = lenLocals.get(currentLenVariable);
		currentLenVariable++;
		return lenLocal;
	}

	/**
	 * Materializes the next node of 'var' by replacing the outgoing edge with two
	 * edges connected by a new node. The first edge has length 1 and the second
	 * also has length 1. This represents the case where the list outgoing from
	 * 'var' has length exactly 2.
	 */
	public SLLGraph focusOne(SLLGraph graph, Local var) {
		SLLGraph result = graph.copy();
		Node rhsNode = result.pointsTo(var);
		Node rhsNextNode = rhsNode.next;
		Node newNextNode = new Node(rhsNextNode);
		result.addNode(newNextNode);
		rhsNode.next = newNextNode;
		result.normalize();
		result.addSizeEqualsFactoids(newNextNode, 1);
		result.sizes.removeVar(rhsNode.edgeLen);
		result.addSizeEqualsFactoids(rhsNode, 1);
		return result;
	}

	/**
	 * Materializes the next node of 'var' by replacing the outgoing edge with two
	 * edges connected by a new node. The first edge has length 1 and the second has
	 * length >1. This represents the case where the list outgoing from 'var' has
	 * length >2.
	 */
	public SLLGraph focusGtOne(SLLGraph graph, Local var) {
		SLLGraph result = graph.copy();
		Node rhsNode = result.pointsTo(var);
		Node rhsNextNode = rhsNode.next;
		Node newNextNode = new Node(rhsNextNode);
		result.addNode(newNextNode);
		rhsNode.next = newNextNode;
		result.normalize();
		result.addSizeFactoid(newNextNode, 2, true); // GTONE
		result.sizes.removeVar(rhsNode.edgeLen);
		result.addSizeEqualsFactoids(rhsNode, 1);
		result.sizes.addFactoid(rhsNode.edgeLen, newNextNode.edgeLen, IntConstant.v(-1)); // rhsNode-newNode<=-1 === newNode-rhsNode>=1
		return result;
	}

	/**
	 * Replaces non-maximal (uninterrupted) list segments with a single maximal list
	 * segment of length >1 and then removes garbage nodes.
	 */
	public SLLGraph generalize(SLLGraph graph) {
		SLLGraph result = graph;

		boolean change = true;
		while (change) {
			change = false;
			result = result.copy();
			for (Node n : result.nodes) {
				if (n == result.nullNode)
					continue;
				// Self-loops are a special case.
				if (n.next == n)
					continue;
				if (n.next == result.nullNode)
					continue;
				boolean isNextInterruption = !n.next.pointedBy.isEmpty() || result.getPreds(n.next).size() > 1;
				if (!isNextInterruption) {
					change = true;
					Node nextNode = n.next.next;
					n.next = nextNode;
					result.addSizeFactoid(nextNode, 1, true);
				}
			}
		}

		result.removeGarbageNodes();
		return result;
	}

	/**
	 * Singleton pattern.
	 */
	private SLLDomain() {
		top = new DisjunctiveState<SLLGraph>() {
			@Override
			public int size() {
				throw new UnsupportedOperationException();
			}

			@Override
			public Iterator<SLLGraph> iterator() {
				throw new UnsupportedOperationException();
			}

			@Override
			public Set<SLLGraph> getDisjuncts() {
				throw new UnsupportedOperationException();
			}

			@Override
			public String toString() {
				return "true";
			}
		};

		bottom = new DisjunctiveState<SLLGraph>();

	}

	/**
	 * A helper class for matching transformers to statements.
	 * 
	 * @author romanm
	 */
	protected class SLLMatcher extends TransformerMatcher<DisjunctiveState<SLLGraph>> {
		@Override
		public void caseInvokeStmt(InvokeStmt stmt) {
			InvokeExpr expr = stmt.getInvokeExpr();
			String methodName = expr.getMethod().getName();
			if (methodName.equals("analysisInitAllNulls")) {
				transformer = new InitAllNullsTransformer();
			} else if (methodName.equals("analysisInitAcyclic")) {
				if (expr.getArgCount() != 1) {
					throw new Error("initAcyclicList expects one argument, but got " + expr.getArgCount() + "!");
				}
				if (expr.getArg(0) instanceof Local)
					transformer = new InitAcyclicTransformer((Local) expr.getArg(0));
				else
					throw new Error("initAcyclicList expects one argument of type Local, but got "
							+ expr.getArg(0).getClass() + "!");
			} else if (methodName.equals("analysisAssertNotNull")) {
				transformer = new AssertNotNullTransformer((Local) expr.getArg(0));
			} else if (methodName.equals("analysisAssertReachable")) {
				transformer = new AssertReachableTransformer((Local) expr.getArg(0), (Local) expr.getArg(1), (StringConstant) expr.getArg(2));
			} else if (methodName.equals("analysisAssertAcyclic")) {
				transformer = new AssertAcyclicTransformer((Local) expr.getArg(0), (StringConstant) expr.getArg(1));
			} else if (methodName.equals("analysisAssertCyclic")) {
				transformer = new AssertCyclicTransformer((Local) expr.getArg(0), (StringConstant) expr.getArg(1));
			} else if (methodName.equals("analysisAssertDisjoint")) {
				transformer = new AssertDisjointTransformer((Local) expr.getArg(0), (Local) expr.getArg(1), (StringConstant) expr.getArg(2));
			} else if (methodName.equals("analysisAssertNoGarbage")) {
				transformer = new AssertNoGarbageTransformer((StringConstant) expr.getArg(0));
			} else if (methodName.equals("analysisLengthDiff")) {
				transformer = new AssertLengthDiff((Local) expr.getArg(0), (Local) expr.getArg(1),
						(IntConstant) expr.getArg(2), (StringConstant) expr.getArg(3));
			}
		}

		@Override
		public void matchAssignRefToRef(Local lhs, Local rhs) {
			if (isListRefType(lhs) && isListRefType(rhs)) {
				if (lhs.equivTo(rhs))
					transformer = IdOperation.v();
				else
					transformer = new AssignRefToRefTransformer(lhs, rhs);
			}
		}

		@Override
		public void matchAssignNewExprToLocal(AssignStmt stmt, Local lhs, RefType baseType) {
			if (isListRefType(lhs))
				transformer = new AssignNewExprToLocalTransformer(lhs);
		}

		@Override
		public void matchAssignNullToRef(Local lhs) {
			if (isListRefType(lhs))
				transformer = new AssignNullTransformer(lhs);
		}

		/**
		 * Matches statements of the form {@code x=y.f} where 'x' and 'y' are local
		 * variables.
		 */
		@Override
		public void matchAssignInstanceFieldRefToLocal(AssignStmt stmt, Local lhs, Local rhs, SootField field) {
			if (field.getName().equals(listClassField)) {
				transformer = new AssignNextToLocalTransformer(lhs, rhs);
			}
		}

		@Override
		public void matchAssignLocalToInstanceFieldRef(Local base, SootField field, Local rhs) {
			if (isListRefType(base) && field.getName().equals(listClassField)) {
				transformer = new AssignLocalToNextFieldTransformer(base, rhs);
			}
		}

		@Override
		public void matchAssignNullToInstanceFieldRef(Local base, SootField field) {
			if (isListRefType(base))
				transformer = new AssignNextNullTransformer(base);
		}

		@Override
		public void matchAssumeLocalEqNull(IfStmt stmt, boolean polarity, Local op1) {
			transformer = new AssumeLocalEqNullTransformer(polarity, op1);
		}

		@Override
		public void matchAssumeLocalEqLocal(IfStmt stmt, boolean polarity, Local op1, Local op2) {
			transformer = new AssumeLocalEqLocalTransformer(polarity, op1, op2);
		}
	}

	/**
	 * A transformer for statements of the form {@code x=new SLLBenchmarks()}.
	 * 
	 * @author romanm
	 */
	protected class AssignNewExprToLocalTransformer extends UnaryOperation<DisjunctiveState<SLLGraph>> {
		protected final Local lhs;

		public AssignNewExprToLocalTransformer(Local lhs) {
			this.lhs = lhs;
		}

		@Override
		public DisjunctiveState<SLLGraph> apply(DisjunctiveState<SLLGraph> input) {
			Set<SLLGraph> disjuncts = new HashSet<>();
			for (SLLGraph graph : input) {
				SLLGraph disjunct = graph.copy();
				disjunct.unmapLocal(lhs);
				Node newNode = new Node(disjunct.nullNode);
				disjunct.addNode(newNode);
				disjunct.mapLocal(lhs, newNode);
				disjunct.normalize();
				disjunct.addSizeEqualsFactoids(newNode, 1);
				disjuncts.add(disjunct);
			}
			DisjunctiveState<SLLGraph> result = new DisjunctiveState<>(disjuncts);
			return result;
		}
	}

	/**
	 * A transformer for statements of the form {@code x=null}.
	 * 
	 * @author romanm
	 */
	protected class AssignNullTransformer extends UnaryOperation<DisjunctiveState<SLLGraph>> {
		protected final Local lhs;

		public AssignNullTransformer(Local lhs) {
			this.lhs = lhs;
		}

		@Override
		public DisjunctiveState<SLLGraph> apply(DisjunctiveState<SLLGraph> input) {
			Set<SLLGraph> disjuncts = new HashSet<>();
			for (SLLGraph graph : input) {
				SLLGraph disjunct = graph.copy();
				disjunct.unmapLocal(lhs);
				disjunct.mapLocal(lhs, disjunct.nullNode);
				disjunct.normalize();
				disjuncts.add(disjunct);
			}
			DisjunctiveState<SLLGraph> result = new DisjunctiveState<>(disjuncts);
			return result;
		}
	}

	/**
	 * A transformer for statements of the form {@code x=y}.
	 * 
	 * @author romanm
	 */
	protected class AssignRefToRefTransformer extends UnaryOperation<DisjunctiveState<SLLGraph>> {
		protected final Local lhs;
		protected final Local rhs;

		public AssignRefToRefTransformer(Local lhs, Local rhs) {
			this.lhs = lhs;
			this.rhs = rhs;
		}

		@Override
		public DisjunctiveState<SLLGraph> apply(DisjunctiveState<SLLGraph> input) {
			Set<SLLGraph> disjuncts = new HashSet<>();
			for (SLLGraph graph : input) {
				SLLGraph disjunct = graph.copy();
				disjunct.unmapLocal(lhs);
				disjunct.mapLocal(lhs, disjunct.pointsTo(rhs));
				disjunct.normalize();
				disjuncts.add(disjunct);
			}
			DisjunctiveState<SLLGraph> result = new DisjunctiveState<>(disjuncts);
			return result;
		}
	}

	/**
	 * A transformer for statements of the form {@code x=y.next}.
	 * 
	 * @author romanm
	 */
	protected class AssignNextToLocalTransformer extends UnaryOperation<DisjunctiveState<SLLGraph>> {
		protected final Local lhs;
		protected final Local rhs;

		public AssignNextToLocalTransformer(Local lhs, Local rhs) {
			this.lhs = lhs;
			this.rhs = rhs;
		}

		@Override
		public DisjunctiveState<SLLGraph> apply(DisjunctiveState<SLLGraph> input) {
			Set<SLLGraph> disjuncts = new HashSet<>();
			for (SLLGraph graph : input) {
				Node rhsNode = graph.pointsTo(rhs);
				if (rhsNode == graph.nullNode) {
					// Skip this graph as it raises a NullPointerException.
				} else if (graph.checkIfEdgeLenEquals(rhsNode, 1)) {
					SLLGraph disjunct = graph.copy();
					Node rhsNextNode = disjunct.pointsTo(rhs).next;
					disjunct.unmapLocal(lhs);
					disjunct.mapLocal(lhs, rhsNextNode);
					disjunct.normalize();
					disjuncts.add(disjunct);
				} else {
					// Focus on the edge.
					SLLGraph focusOne = focusOne(graph, rhs);
					Node rhsNextNode = focusOne.pointsTo(rhs).next;
					focusOne.unmapLocal(lhs);
					focusOne.mapLocal(lhs, rhsNextNode);
					focusOne.normalize();
					disjuncts.add(focusOne);

					SLLGraph focusGtOne = focusGtOne(graph, rhs);
					rhsNextNode = focusGtOne.pointsTo(rhs).next;
					focusGtOne.unmapLocal(lhs);
					focusGtOne.mapLocal(lhs, rhsNextNode);
					focusGtOne.normalize();
					disjuncts.add(focusGtOne);
				}
			}
			DisjunctiveState<SLLGraph> result = new DisjunctiveState<>(disjuncts);
			return result;
		}
	}

	/**
	 * A transformer for statements of the form {@code x.n=null}.
	 * 
	 * @author romanm
	 */
	protected class AssignNextNullTransformer extends UnaryOperation<DisjunctiveState<SLLGraph>> {
		protected final Local lhs;

		public AssignNextNullTransformer(Local lhs) {
			this.lhs = lhs;
		}

		@Override
		public DisjunctiveState<SLLGraph> apply(DisjunctiveState<SLLGraph> input) {
			Set<SLLGraph> disjuncts = new HashSet<>();
			for (SLLGraph graph : input) {
				Node lhsNode = graph.pointsTo(lhs);
				if (lhsNode == graph.nullNode) {
					// Skip this graph as it raises a NullPointerException.
				} else {
					SLLGraph disjunct = graph.copy();
					lhsNode.next = disjunct.nullNode;
					disjunct.normalize();
					disjunct.addSizeEqualsFactoids(lhsNode, 1);
					disjuncts.add(disjunct);
				}
			}
			DisjunctiveState<SLLGraph> result = new DisjunctiveState<>(disjuncts);
			return result;
		}
	}

	/**
	 * A transformer for statements of the form {@code x.n=y}.
	 * 
	 * @author romanm
	 */
	protected class AssignLocalToNextFieldTransformer extends UnaryOperation<DisjunctiveState<SLLGraph>> {
		protected final Local lhs;
		protected final Local rhs;

		public AssignLocalToNextFieldTransformer(Local lhs, Local rhs) {
			this.lhs = lhs;
			this.rhs = rhs;
		}

		@Override
		public DisjunctiveState<SLLGraph> apply(DisjunctiveState<SLLGraph> input) {
			Set<SLLGraph> disjuncts = new HashSet<>();
			for (SLLGraph graph : input) {
				if (graph.pointsTo(lhs) == graph.nullNode) {
					// Skip this graph as it raises a NullPointerException.
				} else {
					SLLGraph disjunct = graph.copy();
					Node lhsNode = disjunct.pointsTo(lhs);
					Node rhsNode = disjunct.pointsTo(rhs);
					lhsNode.next = rhsNode;
					disjunct.normalize();
					disjunct.addSizeEqualsFactoids(lhsNode, 1);
					disjuncts.add(disjunct);
				}
			}
			DisjunctiveState<SLLGraph> result = new DisjunctiveState<>(disjuncts);
			return result;
		}
	}

	/**
	 * A transformer that always returns a state containing a single shape graph
	 * where all list variables point to null.
	 * 
	 * @author romanm
	 */
	protected class InitAllNullsTransformer extends UnaryOperation<DisjunctiveState<SLLGraph>> {
		@Override
		public DisjunctiveState<SLLGraph> apply(DisjunctiveState<SLLGraph> input) {
			return initNulls();
		}
	}

	/**
	 * A transformer that always returns a state containing three shape graphs where
	 * all list variables point to null, except a given list variable, which points
	 * to an acyclic list of size >= 0.
	 * 
	 * @author romanm
	 */
	protected class InitAcyclicTransformer extends UnaryOperation<DisjunctiveState<SLLGraph>> {
		protected final Local var;

		public InitAcyclicTransformer(Local var) {
			this.var = var;
		}

		@Override
		public DisjunctiveState<SLLGraph> apply(DisjunctiveState<SLLGraph> input) {
			return initAcyclic(var);
		}
	}

	/**
	 * A transformer that checks whether a given list reference variable is/isn't
	 * null.
	 * 
	 * @author romanm
	 */
	protected class AssumeLocalEqNullTransformer extends AssumeTransformer<DisjunctiveState<SLLGraph>> {
		protected final Local var;

		public AssumeLocalEqNullTransformer(boolean polarity, Local var) {
			super(polarity);
			this.var = var;
		}

		@Override
		public DisjunctiveState<SLLGraph> apply(DisjunctiveState<SLLGraph> input) {
			Set<SLLGraph> disjuncts = new HashSet<>();
			for (SLLGraph graph : input) {
				boolean varEqNull = graph.pointsTo(var) == graph.nullNode;
				if (varEqNull == polarity) {
					graph.normalize();
					disjuncts.add(graph);
				}
			}
			DisjunctiveState<SLLGraph> result = new DisjunctiveState<>(disjuncts);
			return result;
		}
	}

	/**
	 * A transformer that checks whether two given list reference variables are
	 * equal, i.e., both reference the same node or both are null.
	 * 
	 * @author romanm
	 */
	protected class AssumeLocalEqLocalTransformer extends AssumeTransformer<DisjunctiveState<SLLGraph>> {
		protected final Local lhs;
		protected final Local rhs;

		public AssumeLocalEqLocalTransformer(boolean polarity, Local lhs, Local rhs) {
			super(polarity);
			this.lhs = lhs;
			this.rhs = rhs;
		}

		@Override
		public DisjunctiveState<SLLGraph> apply(DisjunctiveState<SLLGraph> input) {
			Set<SLLGraph> disjuncts = new HashSet<>();
			for (SLLGraph graph : input) {
				boolean conditionHolds = graph.pointsTo(lhs) == graph.pointsTo(rhs);
				if (conditionHolds == polarity) {
					graph.normalize();
					disjuncts.add(graph);
				}
			}
			DisjunctiveState<SLLGraph> result = new DisjunctiveState<>(disjuncts);
			return result;
		}
	}

	/**
	 * A transformer used for asserting that a variable is not null.
	 * 
	 * @author romanm
	 */
	protected class AssertNotNullTransformer extends AssumeLocalEqNullTransformer {

		public AssertNotNullTransformer(Local var) {
			super(true, var);
		}

		public AssertNotNullTransformer(boolean polarity, Local var) {
			super(polarity, var);
		}
	}

	/**
	 * Our length-diff transformer
	 * 
	 * @author saars & nevoma
	 */
	class AssertLengthDiff extends UnaryOperation<DisjunctiveState<SLLGraph>> {

		protected final Local first;
		protected final Local second;
		protected final IntConstant diff;
		protected final StringConstant message;

		protected class IncorrectLengthDiffState extends DisjunctiveState<SLLGraph> implements ErrorState {

			public IncorrectLengthDiffState() {
				super();
			}
			
			@Override
			public String getMessages() {
				return message.value;
			}

		}

		public AssertLengthDiff(Local first, Local second, IntConstant diff, StringConstant message) {
			this.first = first;
			this.second = second;
			this.diff = diff;
			this.message = message;
		}

		@Override
		public DisjunctiveState<SLLGraph> apply(DisjunctiveState<SLLGraph> input) {
			Set<SLLGraph> disjuncts = new HashSet<>();
			
			for (SLLGraph graph : input) {
				boolean found = false;
				ZoneState reduced = ZoneDomain.v().reduce(graph.sizes); // imply all possible factoids
				Node n1 = graph.pointsTo(first);
				Node n2 = graph.pointsTo(second);
				if (n1 == null || n2 == null || reduced == ZoneDomain.v().getTop())
				{
					graph.normalize();
					disjuncts.add(graph);
					continue;
				}
				
				ZoneFactoid factToLookFor = new ZoneFactoid(n1.edgeLen, n2.edgeLen, diff);
				for (ZoneFactoid f : reduced.getFactoids()) {
					if (f.eq(factToLookFor)) {
						disjuncts.add(graph);
						found = true;
						break;
					}
				}

				if (!found)
					return new IncorrectLengthDiffState();
			}
			return new DisjunctiveState<>(disjuncts);
		}
	}
	
	/**
	 * Assert no garbage transformer
	 * 
	 * @author saars & nevoma
	 */
	class AssertNoGarbageTransformer extends UnaryOperation<DisjunctiveState<SLLGraph>> {

		protected final StringConstant message;

		protected class GarbageExistsState extends DisjunctiveState<SLLGraph> implements ErrorState {

			public GarbageExistsState() {
				super();
			}
			
			@Override
			public String getMessages() {
				return message.value;
			}

		}

		public AssertNoGarbageTransformer(StringConstant message) {
			this.message = message;
		}

		@Override
		public DisjunctiveState<SLLGraph> apply(DisjunctiveState<SLLGraph> input) {
			Set<SLLGraph> disjuncts = new HashSet<>();
			
			for (SLLGraph graph : input) {
				for (Node n1 : graph.nodes) {
					if (n1 == graph.nullNode) {
						continue;
					}
					if (n1.pointedBy.isEmpty()) {
						boolean foundPrev = false;
						for (Node n2 : graph.nodes) {
							if (n2.next == n1)
							{
								foundPrev = true;
								break;
							}
						}
						if (!foundPrev) {
							return new GarbageExistsState();
						}
					}
				}
				disjuncts.add(graph);
			}
			
			return new DisjunctiveState<>(disjuncts);
		}
	}
}

/**
 * Our assert reachable transformer
 * 
 * @author saars & nevoma
 */
class AssertReachableTransformer extends UnaryOperation<DisjunctiveState<SLLGraph>> {

	protected final Local first;
	protected final Local second;
	protected final StringConstant message;

	protected class NotReachableState extends DisjunctiveState<SLLGraph> implements ErrorState {

		public NotReachableState() {
			super();
		}
		
		@Override
		public String getMessages() {
			return message.value;
		}

	}

	public AssertReachableTransformer(Local first, Local second, StringConstant message) {
		this.first = first;
		this.second = second;
		this.message = message;
	}

	@Override
	public DisjunctiveState<SLLGraph> apply(DisjunctiveState<SLLGraph> input) {
		Set<SLLGraph> disjuncts = new HashSet<>();
		
		for (SLLGraph graph : input) {
			boolean found = false;
			Node curr = graph.pointsTo(first);
			Node target = graph.pointsTo(second);
			while (curr != null) {
				if (curr == target) {
					found = true;
					break;
				}
				curr = curr.next;
			}

			if (!found) {
				return new NotReachableState();
			}
		
			disjuncts.add(graph);
		}
		return new DisjunctiveState<>(disjuncts);
	}
}

/**
 * Our assert disjoint transformer
 * 
 * @author saars & nevoma
 */
class AssertDisjointTransformer extends UnaryOperation<DisjunctiveState<SLLGraph>> {

	protected final Local first;
	protected final Local second;
	protected final StringConstant message;

	protected class NotDisjointState extends DisjunctiveState<SLLGraph> implements ErrorState {

		public NotDisjointState() {
			super();
		}
		
		@Override
		public String getMessages() {
			return message.value;
		}

	}

	public AssertDisjointTransformer(Local first, Local second, StringConstant message) {
		this.first = first;
		this.second = second;
		this.message = message;
	}

	@Override
	public DisjunctiveState<SLLGraph> apply(DisjunctiveState<SLLGraph> input) {
		Set<SLLGraph> disjuncts = new HashSet<>();
		
		for (SLLGraph graph : input) {
			int firstLen = 0;
			int secondLen = 0;
			Node currX = graph.pointsTo(first);
			Node currY = graph.pointsTo(second);

			while (currX != null)
			{
				firstLen++;
				currX = currX.next;
			}
			while (currY != null)
			{
				secondLen++;
				currY = currY.next;
			}
			
			Node longer, shorter;
			if (firstLen > secondLen) {
				longer = graph.pointsTo(first);
				shorter = graph.pointsTo(second);
			}
			else {
				shorter = graph.pointsTo(first);
				longer = graph.pointsTo(second);
			}
			
			int lenDiff = Math.abs(firstLen - secondLen);
			while(lenDiff > 0) {
				longer = longer.next;
				lenDiff--;
			}
			
			while (longer != graph.nullNode) {
				if (longer == shorter)
					return new NotDisjointState();
				longer = longer.next;
				shorter = shorter.next;
			}
		}
		return new DisjunctiveState<>(disjuncts);
	}
}

/**
 * Our assert cyclic transformer
 * 
 * @author saars & nevoma
 */
class AssertCyclicTransformer extends UnaryOperation<DisjunctiveState<SLLGraph>> {

	protected final Local var;
	protected final StringConstant message;

	protected class NotCyclicState extends DisjunctiveState<SLLGraph> implements ErrorState {

		public NotCyclicState() {
			super();
		}
		
		@Override
		public String getMessages() {
			return message.value;
		}

	}

	public AssertCyclicTransformer(Local var, StringConstant message) {
		this.var = var;
		this.message = message;
	}

	@Override
	public DisjunctiveState<SLLGraph> apply(DisjunctiveState<SLLGraph> input) {
		Set<SLLGraph> disjuncts = new HashSet<>();
		
		for (SLLGraph graph : input) {
			boolean found = false;
			Node curr = graph.pointsTo(var);
			Node target = curr;
			while (curr != null) {
				if (curr.next == target) {
					found = true;
					break;
				}
				curr = curr.next;
			}

			if (!found) {
				return new NotCyclicState();
			}
			
			disjuncts.add(graph);
		}
		return new DisjunctiveState<>(
				disjuncts);
	}
}

/**
 * Our assert acyclic transformer
 * 
 * @author saars & nevoma
 */
class AssertAcyclicTransformer extends UnaryOperation<DisjunctiveState<SLLGraph>> {

	protected final Local var;
	protected final StringConstant message;

	protected class NotAcyclicState extends DisjunctiveState<SLLGraph> implements ErrorState {

		public NotAcyclicState() {
			super();
		}
		
		@Override
		public String getMessages() {
			return message.value;
		}

	}

	public AssertAcyclicTransformer(Local var, StringConstant message) {
		this.var = var;
		this.message = message;
	}

	@Override
	public DisjunctiveState<SLLGraph> apply(DisjunctiveState<SLLGraph> input) {
		Set<SLLGraph> disjuncts = new HashSet<>();
		
		for (SLLGraph graph : input) {
			boolean found = false;
			Node curr = graph.pointsTo(var);
			Node target = curr;
			while (curr != null) {
				if (curr.next == target) {
					found = true;
					break;					
				}
				curr = curr.next;
			}

			if (found) {
				return new NotAcyclicState(); 
			}
			
			disjuncts.add(graph);
		}
		return new DisjunctiveState<>(disjuncts);
	}
}