package base;

import java.io.File;
import analysis.VulnerabilityReporter;
import soot.G;
import soot.PackManager;
import soot.Scene;
import soot.SootClass;
import soot.Transform;
import soot.Transformer;
import soot.options.Options;

public abstract class TestSetup {
	protected static VulnerabilityReporter reporter;

	protected void executeStaticAnalysis(String targetTestClassName) {
		setupSoot(targetTestClassName);
		registerSootTransformers();
		executeSootTransformers();
	}

	private void executeSootTransformers() {
		// This will run the intra-procedural analysis
		PackManager.v().runBodyPacks();
	}

	private void registerSootTransformers() {
		// add the analysis to jimple transform pack (jtp)
		Transform transform = new Transform("jtp.analysis", createAnalysisTransformer());
		PackManager.v().getPack("jtp").add(transform);
	}
	
	protected abstract Transformer createAnalysisTransformer();
	
	/*
	 * This method provides the options to soot to analyze the respective classes.
	 */
	protected static void setupSoot(String targetTestClassName) {
		G.reset();
		String userdir = System.getProperty("user.dir");
		String sootCp = userdir + File.separator + "target" + File.separator + "test-classes"+ File.pathSeparator + "lib"+File.separator+"rt.jar";
		Options.v().set_whole_program(true);
		Options.v().set_soot_classpath(sootCp);
		Options.v().set_no_bodies_for_excluded(true);
		Options.v().process_dir();
		Options.v().set_allow_phantom_refs(true);
		Options.v().setPhaseOption("jb", "use-original-names:true");
		Options.v().set_prepend_classpath(false);
		SootClass c = Scene.v().forceResolve(targetTestClassName, SootClass.BODIES);
		if (c != null)
			c.setApplicationClass();
		Scene.v().loadNecessaryClasses();
	}
}
