/**
 * List-manipulating methods to test the shape analysis.
 * 
 * You may run this example with the following command-line arguments:<br>
 * <code>java bgu.cs.absint.analyses.sllSize.SLLMain -cp . -pp -f jimple -p jb use-original-names -p jb.ls enabled:false -p jb.ls enabled:false -keep-line-number -print-tags SLLSizeBenchmarks</code>
 * 
 * @author romanm
 */
public class MySLLSizeBenchmarks {
	public static class Node {
		public Node next;
		public int data;
	}

	///////////////////////////////////////////////////////////////////////////
	// Analysis helper methods.
	///////////////////////////////////////////////////////////////////////////

	/**
	 * The postcondition of this method is a state where all variables point to
	 * null, except 'x', which points to a list of size >=0.
	 */
	public static void analysisInitAcyclic(Node x) {
	}

	/**
	 * The postcondition of this method is a state where all variables point to
	 * null.
	 */
	public static void analysisInitAllNulls() {
	}

	/**
	 * Asserts that 'x' is not null.<br>
	 */
	public static void analysisAssertNotNull(Node x, String message) {
	}

	/**
	 * Asserts that s'y' is reachable from 'x'. That is, starting from 'x' and
	 * following 'next' fields gets to a node referenced by 'y', or to null when 'y'
	 * is null.<br>
	 */
	public static void analysisAssertReachable(Node x, Node y, String message) {
	}

	/**
	 * Asserts that 'x' and 'y' are disjoint. That is, following 'next' fields from
	 * 'x' and from 'y' does not lead to a common node.<br>
	 */
	public static void analysisAssertDisjoint(Node x, Node y, String message) {
	}

	/**
	 * Asserts that the list starting from 'x' is acyclic. That is, starting from
	 * 'x' and following the 'next' field eventually gets you to null.<br>
	 */
	public static void analysisAssertAcyclic(Node x, String message) {
	}

	/**
	 * Asserts that 'x' references a cyclic list. That is, starting from 'x' and
	 * following the 'next' field gets you back to 'x'.<br>
	 */
	public static void analysisAssertCyclic(Node x, String message) {
	}

	/**
	 * Asserts that all list node are reachable from some variable. Note that this
	 * analysis can only be effectively used within loop bodies, as garbage nodes
	 * are automatically collected at loop heads as part of the abstraction. The
	 * best place therefore to have this assertion is as the last statement of a
	 * loop.<br>
	 */
	public static void analysisAssertNoGarbage(String message) {
	}

	/**
	 * Asserts that the difference between the length of the list segment from list1
	 * and the list segment from list2 is less than diff.
	 */
	public static void analysisLengthDiff(Node list1, Node list2, int diff, String message) {
	}

	///////////////////////////////////////////////////////////////////////////
	// End of analysis helper methods.
	///////////////////////////////////////////////////////////////////////////

	/**
	 * Like createAndPrint, but the second diff assert shouldn't pass 
	 */
	public Node createAndPrintError(int size) {
		analysisInitAllNulls();
		Node head1 = null;
		Node head2 = null;
		for (int i = 0; i < size; ++i) {
			Node n1 = new Node();
			n1.next = head1;
			n1.data = i;
			head1 = n1;

			Node n2 = new Node();
			n2.next = head2;
			n2.data = i;
			head2 = n2;
			
			analysisAssertNoGarbage("Unable to prove absence of garbage in create!");
		}
		
		analysisLengthDiff(head1, head2, 5, "Unable to assert size difference!"); // pass
		analysisLengthDiff(head2, head1, -5, "Unable to assert size difference!"); // fail

		Node t1 = head1;
		Node t2 = head2;
		while (t1 != null) {
			//System.out.println(t1.data);
			//System.out.println(t2.data);
			t1 = t1.next;
			// Since we know that the two lists have the same length, the next dereference
			// is safe.
			t2 = t2.next;
		}
		return head1;
	}
	
	/**
	 * Creates an acylic list and assert its state.
	 * 
	 */
	public Node testAcyclic(Node head) {
		analysisInitAcyclic(head); // Start with an acyclic list.

		analysisAssertAcyclic(head, "Not acyclic!");
		//analysisAssertCyclic(head, "Not cyclic!"); // gives an error as expected!

		return null; // to prevent another error when the assertion fails
	}
	
	/**
	 * Creates a cylic list and assert its state.
	 * 
	 */
	public Node testCyclic(Node head) {
		analysisInitAcyclic(head); // Start with an acyclic list.
		Node curr = head;
		while (curr.next != null) {
			curr = curr.next;
		}
		curr.next = head; // creates the cycle
		analysisAssertCyclic(head, "Not cyclic!");
		//analysisAssertAcyclic(head, "Not acyclic!"); // gives an error as expected!

		return null; // to prevent another error when the assertion fails
	}
	
	/**
	 * Creates a list and assert y is reachable from head.
	 * 
	 */
	public Node testReachable(Node head) {
		analysisInitAcyclic(head); // Start with an acyclic list.
		Node y = new Node();
		head.next = y;
		
		analysisAssertReachable(head, y, "Not reachable!");
		//analysisAssertDisjoint(head, y, "Not disjoint!"); // gives an error as expected!

		return null; // to prevent another error when the assertion fails
	}
	
	/**
	 * Creates a list and assert y is unreachable from head.
	 * 
	 */
	public Node testDisjoint(Node head) {
		analysisInitAcyclic(head); // Start with an acyclic list.
		Node y = new Node();
		
		analysisAssertDisjoint(head, y, "Not disjoint!");
		//analysisAssertReachable(head, y, "Not reachable!"); // gives an error as expected!

		return null; // to prevent another error when the assertion fails
	}
}