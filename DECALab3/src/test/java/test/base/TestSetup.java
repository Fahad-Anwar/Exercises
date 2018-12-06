package test.base;

import java.io.File;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;

import analysis.IFDSTaintAnalysisProblem;
import analysis.TaintAnalysisFlowFunctions;
import analysis.VulnerabilityReporter;
import analysis.fact.DataFlowFact;
import heros.EdgeFunction;
import heros.InterproceduralCFG;
import soot.G;
import soot.PackManager;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootMethod;
import soot.Transform;
import soot.Transformer;
import soot.Unit;
import soot.jimple.toolkits.ide.JimpleIFDSSolver;
import soot.jimple.toolkits.ide.icfg.JimpleBasedInterproceduralCFG;
import soot.options.Options;

public abstract class TestSetup {
	protected VulnerabilityReporter reporter;
	protected TaintAnalysisFlowFunctions flowFunctions;
	private Multimap<Unit, DataFlowFact> dataFlowFactsAtStmt = HashMultimap.create();
	
	/*
	 * Checks that the IFDS solver generates the dataflow fact "fact" at the statement "stmt". 
	 * For simplification we test based on toString() representations of the objects. 
	 */
	protected boolean containsDataFlowFactAtStmt(String fact, String stmt){
		for(Entry<Unit, DataFlowFact> e : dataFlowFactsAtStmt.entries()){
			if(e.getKey().toString().equals(stmt) && e.getValue().toString().equals(fact)){
				return true;
			}
		}
		return false;
	}
	

	protected void executeStaticAnalysis(String targetTestClassName) {
		setupSoot(targetTestClassName);
		registerSootTransformers();
		executeSootTransformers();
	}

	private void executeSootTransformers() {
		//Apply all necessary packs of soot. This will execute the respective Transformer
		PackManager.v().getPack("cg").apply();
		PackManager.v().getPack("wjtp").apply();
	}

	private void registerSootTransformers() {
		Transform transform = new Transform("wjtp.ifds", createAnalysisTransformer());
		PackManager.v().getPack("wjtp").add(transform);
	}

	private Transformer createAnalysisTransformer() {
		return new SceneTransformer() {
			@Override
			protected void internalTransform(String phaseName, Map<String, String> options) {
				JimpleBasedInterproceduralCFG icfg = new JimpleBasedInterproceduralCFG(false);
				flowFunctions.setICFG(icfg);
				IFDSTaintAnalysisProblem problem = new IFDSTaintAnalysisProblem(icfg, flowFunctions);
				JimpleIFDSSolver<DataFlowFact, InterproceduralCFG<Unit, SootMethod>> solver = new JimpleIFDSSolver<DataFlowFact, InterproceduralCFG<Unit, SootMethod>>(problem){
					

					@Override
					protected void propagate(DataFlowFact arg0, Unit stmt, DataFlowFact fact,
							EdgeFunction<heros.solver.IFDSSolver.BinaryDomain> arg3, Unit arg4, boolean arg5) {
						dataFlowFactsAtStmt.put(stmt, fact);
						super.propagate(arg0, stmt, fact, arg3, arg4, arg5);
					}
				};
				solver.solve();
			}
		};
	}
	/*
	 * This method provides the options to soot to analyse the respecive
	 * classes.
	 */
	private void setupSoot(String targetTestClassName) {
		G.reset();
		String userdir = System.getProperty("user.dir");
		String sootCp = userdir + File.separator + "target" + File.separator + "test-classes"+ File.pathSeparator + "lib"+File.separator+"rt.jar";
		Options.v().set_soot_classpath(sootCp);

		// We want to perform a whole program, i.e. an interprocedural analysis.
		// We construct a basic CHA call graph for the program
		Options.v().set_whole_program(true);
		Options.v().setPhaseOption("cg.cha", "on");
		Options.v().setPhaseOption("cg", "all-reachable:true");

		Options.v().set_no_bodies_for_excluded(true);
		Options.v().set_allow_phantom_refs(true);
		Options.v().setPhaseOption("jb", "use-original-names:true");
		Options.v().set_prepend_classpath(false);

		Scene.v().addBasicClass("java.lang.StringBuilder");
		SootClass c = Scene.v().forceResolve(targetTestClassName, SootClass.BODIES);
		if(c != null)
			c.setApplicationClass();
		Scene.v().loadNecessaryClasses();
	}
}
