package exercises;

import analysis.CallGraph;
import analysis.exercise1.CHAAlgorithm;
import analysis.exercise2.RTAAlgorithm;
import base.TestSetup;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import soot.*;

import java.util.Map;
import java.util.Set;

public class RTATest extends TestSetup {

    private Scene scene;
    private CallGraph cg;
    private SootMethod interfaceMethod;
    private SootMethod superclassMethod;
    private SootMethod subclassMethod;
    private SootMethod intermediateMethod;
    private SootMethod leafMethod;
    private SootMethod otherLeafMethod;
    private SootMethod specializationMethod;
    private SootMethod thirdLeafMethod;
    private SootMethod fourthLeafMethod;

    private SootMethod mainMethod;

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
        interfaceMethod = scene.getMethod("<target.exercise2.SomeInterface: void doSomething()>");
        superclassMethod = scene.getMethod("<target.exercise2.Superclass: void doSomething()>");
        subclassMethod = scene.getMethod("<target.exercise2.Subclass: void doSomething()>");
        intermediateMethod = scene.getMethod("<target.exercise2.IntermediateClass: void doSomething()>");
        leafMethod = scene.getMethod("<target.exercise2.LeafClass: void doSomething()>");
        otherLeafMethod = scene.getMethod("<target.exercise2.OtherLeafClass: void doSomething()>");
        specializationMethod = scene.getMethod("<target.exercise2.Specialization: void doSomething()>");
        thirdLeafMethod = scene.getMethod("<target.exercise2.ThirdLeafClass: void doSomething()>");
        fourthLeafMethod = scene.getMethod("<target.exercise2.FourthLeafClass: void doSomething()>");


        mainMethod = scene.getMethod("<target.exercise2.Starter: void main(java.lang.String[])>");


        RTAAlgorithm rta = new RTAAlgorithm();
        cg = rta.constructCallGraph(scene);
    }

    @Test
    public void genericCall() {
        Set<SootMethod> callsFromMain = cg.edgesOutOf(mainMethod);

        // things actually instantiated
        Assert.assertTrue(callsFromMain.contains(leafMethod));
        Assert.assertTrue(callsFromMain.contains(otherLeafMethod));
        Assert.assertTrue(callsFromMain.contains(specializationMethod));
        Assert.assertTrue(callsFromMain.contains(subclassMethod));

        // things that aren't instantiated
        Assert.assertFalse(callsFromMain.contains(thirdLeafMethod));
        Assert.assertFalse(callsFromMain.contains(fourthLeafMethod));
    }

}
