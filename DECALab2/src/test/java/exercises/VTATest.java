package exercises;

import analysis.CallGraph;
import analysis.exercise3.VTAAlgorithm;
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

public class VTATest extends TestSetup {
    private Scene scene;
    private CallGraph cg;
    private SootMethod scenarioMain;

    @Override
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

        scenarioMain = scene.getMethod("<target.exercise3.SimpleScenario: void main(java.lang.String[])>");


        VTAAlgorithm vta = new VTAAlgorithm();
        cg = vta.constructCallGraph(scene);
    }

    @Test
    public void testScenario() {
        Set<SootMethod> callsFromMain = cg.edgesOutOf(scenarioMain);
        assertCallExists(callsFromMain, "<target.exercise2.LeafClass: void doSomething()>");
        assertCallExists(callsFromMain, "<target.exercise2.FifthLeafClass: void doSomething()>");
        assertCallExists(callsFromMain, "<target.exercise2.SixthLeafClass: void doSomething()>");

        assertCallMissing(callsFromMain, "<target.exercise2.SomeInterface: void doSomething()>");
        assertCallMissing(callsFromMain, "<target.exercise2.FourthLeafClass: void doSomething()>");
        assertCallMissing(callsFromMain, "<target.exercise2.IntermediateClass: void doSomething()>");
        assertCallMissing(callsFromMain, "<target.exercise2.OtherLeafClass: void doSomething()>");
        assertCallMissing(callsFromMain, "<target.exercise2.Specialization: void doSomething()>");
        assertCallMissing(callsFromMain, "<target.exercise2.Subclass: void doSomething()>");
        assertCallMissing(callsFromMain, "<target.exercise2.Superclass: void doSomething()>");
    }
}
