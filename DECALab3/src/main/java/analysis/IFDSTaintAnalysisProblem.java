package analysis;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

import com.beust.jcommander.internal.Maps;

import analysis.fact.DataFlowFact;
import heros.FlowFunctions;
import heros.InterproceduralCFG;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.toolkits.ide.DefaultJimpleIFDSTabulationProblem;

public class IFDSTaintAnalysisProblem extends DefaultJimpleIFDSTabulationProblem<DataFlowFact,InterproceduralCFG<Unit, SootMethod>>{


	private final TaintAnalysisFlowFunctions flowFunctions;

	public IFDSTaintAnalysisProblem(InterproceduralCFG<Unit, SootMethod> icfg, TaintAnalysisFlowFunctions flowFunctions) {
		super(icfg);
		this.flowFunctions = flowFunctions;
	}

	@Override
	public Map<Unit, Set<DataFlowFact>> initialSeeds() {
		Map<Unit,Set<DataFlowFact>> res = Maps.newHashMap();
		for(SootClass c : Scene.v().getApplicationClasses()){
			for(SootMethod m : c.getMethods()){
				if(!m.hasActiveBody()){
					continue;
				}
				if(m.getName().equals("doGet")){
					res.put(m.getActiveBody().getUnits().getFirst(),Collections.singleton(zeroValue()));
				}
			}
		}
		return res;
	}

	@Override
	protected FlowFunctions<Unit, DataFlowFact, SootMethod> createFlowFunctionsFactory() {
		return flowFunctions;
	}

	@Override
	protected DataFlowFact createZeroValue() {
		return DataFlowFact.zero();
	}

	@Override
	public boolean autoAddZero() {
		return true;
	}
}
