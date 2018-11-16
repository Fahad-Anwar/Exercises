package exercises;

import analysis.CallGraph;
import analysis.exercise1.CHAAlgorithm;
import base.TestSetup;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootMethod;
import soot.Transformer;

import java.util.Map;
import java.util.Set;

public class CHATest extends TestSetup {

	private Scene scene;
	private CallGraph cg;
	private SootMethod exampleMain;
	private SootMethod exampleConstructor;
	private SootMethod subjectConstructor;
	private SootMethod exampleSubjectModify;
	private SootMethod observerableNotifyObservers;
	private SootMethod observerableNotifyObserversSpecific;
	private SootMethod observerUpdate;
	private SootMethod exampleUpdate;


	protected Transformer createAnalysisTransformer() {
		return new SceneTransformer() {
			@Override
			protected void internalTransform(String phaseName, Map<String, String> options) {
				//Scene.v().getApplicationClasses().stream().forEach(c -> System.out.println(c.toString()));
				//Scene.v().getEntryPoints().stream().forEach(c -> System.out.println(c.toString()));

				scene = Scene.v();
			}
		};

	}

	@Before
	public void setUp() throws Exception {
		executeStaticAnalysis();

		exampleMain = scene.getMethod("<target.exercise1.SimpleExample: void main(java.lang.String[])>");
		exampleConstructor = scene.getMethod("<target.exercise1.SimpleExample: void <init>()>");
		subjectConstructor = scene.getMethod("<target.exercise1.SimpleExample$Subject: void <init>()>");
		exampleSubjectModify = scene.getMethod("<target.exercise1.SimpleExample$Subject: void modify()>");
		observerableNotifyObservers = scene.getMethod("<target.exercise1.Observable: void notifyObservers()>");
		observerableNotifyObserversSpecific = scene.getMethod("<target.exercise1.Observable: void notifyObservers(java.lang.Object)>");
		observerUpdate = scene.getMethod("<target.exercise1.Observer: void update(target.exercise1.Observable,java.lang.Object)>");
		exampleUpdate = scene.getMethod("<target.exercise1.SimpleExample: void update(target.exercise1.Observable,java.lang.Object)>");

		CHAAlgorithm cha = new CHAAlgorithm();
		cg = cha.constructCallGraph(scene);
	}

	@Test public void constructorCalls() {
		// static to constructor call
		Set<SootMethod> calledFromMain = cg.edgesOutOf(exampleMain);
		Assert.assertTrue(calledFromMain.contains(exampleConstructor));
		Assert.assertTrue(calledFromMain.contains(subjectConstructor));
	}

	@Test public void staticToInstanceCall() {
		// static to instance call
		Set<SootMethod> calledFromMain = cg.edgesOutOf(exampleMain);
		Assert.assertTrue(calledFromMain.contains(exampleSubjectModify));
	}

	@Test public void instanceToInterfaceMethod() {
		// instance to interface method
		Set<SootMethod> calledFromModify = cg.edgesOutOf(exampleSubjectModify);
		Assert.assertTrue(calledFromModify.contains(observerableNotifyObservers));

		// more specific
		Set<SootMethod> calledFromNotify = cg.edgesOutOf(observerableNotifyObservers);
		Assert.assertTrue(calledFromNotify.contains(observerableNotifyObserversSpecific));
	}

	@Test
	public void polymorphicCallSite() {
		// polymorphic call site (interface)
		Set<SootMethod> calledMethods = cg.edgesOutOf(observerableNotifyObserversSpecific);
		Assert.assertTrue(calledMethods.contains(observerUpdate));
		Assert.assertTrue(calledMethods.contains(exampleUpdate));
	}

}
