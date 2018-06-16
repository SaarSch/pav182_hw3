package bgu.cs.absint.analyses.sllSize;

import soot.Body;
import soot.PackManager;
import soot.Transform;
import bgu.cs.absint.constructor.DisjunctiveState;
import bgu.cs.absint.soot.BaseAnalysis;

/**
 * Adds the singly-linked lists shape analysis transform to Soot.
 * 
 * @author romanm
 */
public class SLLMain {
	public static void main(String[] args) {
		SLLAnalysis analysis = new SLLAnalysis();
		PackManager.v().getPack("jtp")
				.add(new Transform("jtp.SLLAnalysis", analysis));
		soot.Main.main(args);
	}

	public static class SLLAnalysis extends
			BaseAnalysis<DisjunctiveState<SLLGraph>, SLLDomain> {
		public SLLAnalysis() {
			super(SLLDomain.v());
			useWidening(true);
			useNarrowing(true);
		}

		@Override
		protected void analyzeAndTag(Body b) {
			domain.setBodyLocals(b.getLocals());
			domain.setListClass("MySLLSizeBenchmarks$Node", "next"); // Note for Roman! 
			// MySLLSizeBenchmarks$Node has to be changed to SLLSizeBenchmarks$Node in order to test the project on the given examples. 
			super.analyzeAndTag(b);
		}
	}
}