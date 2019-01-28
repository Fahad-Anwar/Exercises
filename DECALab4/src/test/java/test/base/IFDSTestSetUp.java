package test.base;

import analysis.IFDSLinearConstantAnalysisProblem;
import java.io.File;
import java.util.Map;

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

public abstract class IFDSTestSetUp {

    private static JimpleIFDSSolver<?, InterproceduralCFG<Unit, SootMethod>> solved = null;

    protected JimpleIFDSSolver<?, InterproceduralCFG<Unit, SootMethod>> executeStaticAnalysis(String targetTestClassName) {
        setupSoot(targetTestClassName);
        registerSootTransformers();
        executeSootTransformers();
        if (solved == null) {
            throw new NullPointerException("Something went wrong solving the IFDS problem!");
        }
        return solved;
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
                IFDSLinearConstantAnalysisProblem problem = new IFDSLinearConstantAnalysisProblem(icfg);
                @SuppressWarnings({"rawtypes", "unchecked"})
                JimpleIFDSSolver<?, InterproceduralCFG<Unit, SootMethod>> solver = new JimpleIFDSSolver(problem, true);
                solver.solve();
                solved = solver;
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
        if (c != null) {
            c.setApplicationClass();
        }
        Scene.v().loadNecessaryClasses();
    }
}
