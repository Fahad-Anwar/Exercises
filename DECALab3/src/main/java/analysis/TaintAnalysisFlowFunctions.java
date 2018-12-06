package analysis;

import analysis.fact.DataFlowFact;
import heros.FlowFunctions;
import heros.InterproceduralCFG;
import soot.SootMethod;
import soot.Unit;

public abstract class TaintAnalysisFlowFunctions implements FlowFunctions<Unit, DataFlowFact, SootMethod> {
	protected InterproceduralCFG<Unit, SootMethod> icfg;
	public void setICFG(InterproceduralCFG<Unit, SootMethod> icfg){
		this.icfg = icfg;
	}
	
	protected void prettyPrint(Unit stmt, DataFlowFact fact){
		if(icfg.getMethodOf(stmt).toString().contains("doGet"))
			System.out.println("Method :" +icfg.getMethodOf(stmt) +", Stmt: " + stmt +", Fact: " + fact);
	}
}
