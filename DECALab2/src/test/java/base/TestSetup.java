package base;

import com.google.common.collect.Lists;
import org.junit.Assert;
import soot.*;
import soot.options.Options;

import java.io.File;
import java.util.Set;

public abstract class TestSetup {

	protected void executeStaticAnalysis() {
		setupSoot();
		registerSootTransformers();
		executeSootTransformers();
	}


	private void executeSootTransformers() {
		// This will run the intra-procedural analysis
		PackManager.v().runPacks();
	}

	private void registerSootTransformers() {
		// add the analysis to jimple transform pack (jtp)
		Transform transform = new Transform("wjtp.analysis", createAnalysisTransformer());
		PackManager.v().getPack("wjtp").add(transform);
	}

	protected abstract Transformer createAnalysisTransformer();

	/*
	 * This method provides the options to soot to analyze the respective classes.
	 */
	protected static void setupSoot() {
		G.reset();
		String userdir = System.getProperty("user.dir");
		String sootCp = userdir + File.separator + "target" + File.separator + "test-classes"+ File.pathSeparator + "lib"+File.separator+"rt.jar";
		Options.v().set_whole_program(true);
		Options.v().set_soot_classpath(sootCp);
		Options.v().set_no_bodies_for_excluded(true);
		Options.v().set_full_resolver(true);
		Options.v().set_process_dir(Lists.newArrayList(userdir + File.separator + "target" + File.separator + "test-classes"));
		Options.v().set_exclude(Lists.newArrayList("exercises.*", "base.*"));
		Options.v().set_allow_phantom_refs(true);
		Options.v().setPhaseOption("jb", "use-original-names:true");
		Options.v().set_prepend_classpath(false);
		Options.v().set_output_format(Options.output_format_none); // otherwise you won't have everything jimplified  ¯\_(ツ)_/¯


		/*SootClass c = Scene.v().forceResolve(targetTestClassName, SootClass.BODIES);
		if (c != null)
			c.setApplicationClass();
		*/
		Scene.v().loadNecessaryClasses();
	}


    protected static void assertCallExists(Set<SootMethod> calledMethods, String methodSignature) {
        Assert.assertTrue(calledMethods.contains(Scene.v().getMethod(methodSignature)));
    }

    protected static void assertCallMissing(Set<SootMethod> calledMethods, String methodSignature) {
        Assert.assertFalse(calledMethods.contains(Scene.v().getMethod(methodSignature)));
    }
}
