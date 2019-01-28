package test.exercises;

import heros.InterproceduralCFG;
import heros.solver.Pair;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import static org.junit.Assert.fail;
import org.junit.Test;
import soot.Local;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.toolkits.ide.JimpleIDESolver;

import target.exercise1and2.FunctionCall2;
import target.exercise1and2.SimpleAssignment;
import target.exercise1and2.SimpleAssignment2;
import target.exercise1and2.SimpleAssignment3;
import target.exercise1and2.SimpleAssignment4;
import target.exercise1and2.SimpleAssignment5;
import test.base.IDETestSetUp;

public class Exercise2Test extends IDETestSetUp {

    SootMethod getEntryPointMethod() {
        for (SootClass c : Scene.v().getApplicationClasses()) {
            for (SootMethod m : c.getMethods()) {
                if (!m.hasActiveBody()) {
                    continue;
                }
                if (m.getName().equals("entryPoint")) {
                    return m;
                }
            }
        }
        throw new IllegalArgumentException("Method does not exist in scene!");
    }

    void checkResultsAtLastStatement(JimpleIDESolver<?, ?, ? extends InterproceduralCFG<Unit, SootMethod>> analysis, List<Pair<String, Integer>> expectedResult) {
        SootMethod m = getEntryPointMethod();
        Map<?, ?> res = analysis.resultsAt(m.getActiveBody().getUnits().getLast());
        int correctResultCounter = 0;
        for (Pair<String, Integer> expected : expectedResult) {
            for (Map.Entry<?, ?> entry : res.entrySet()) {
                Map.Entry<Local, Integer> e = (Map.Entry<Local, Integer>) entry;
                if (expected.getO1().equals(e.getKey().getName()) && expected.getO2().intValue() == e.getValue().intValue()) {
                    correctResultCounter++;
                }
            }
        }
        if (correctResultCounter != expectedResult.size()) {
            fail("results are not complete or correct");
        }
    }

    @Test
    public void SimpleAssignment() {
        JimpleIDESolver<?, ?, ? extends InterproceduralCFG<Unit, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair("i", 100));
        expected.add(new Pair("j", 200));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void SimpleAssignment2() {
        JimpleIDESolver<?, ?, ? extends InterproceduralCFG<Unit, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment2.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair("i", 100));
        expected.add(new Pair("j", 200));
        expected.add(new Pair("k", 40));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void SimpleAssignment3() {
        JimpleIDESolver<?, ?, ? extends InterproceduralCFG<Unit, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment3.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair("i", 100));
        expected.add(new Pair("j", 200));
        expected.add(new Pair("k", 400));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void SimpleAssignment4() {
        JimpleIDESolver<?, ?, ? extends InterproceduralCFG<Unit, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment4.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair("i", 100));
        expected.add(new Pair("j", 200));
        expected.add(new Pair("k", 413));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void SimpleAssignment5() {
        JimpleIDESolver<?, ?, ? extends InterproceduralCFG<Unit, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment5.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair("i", 13));
        expected.add(new Pair("j", 200));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void FunctionCall2() {
        JimpleIDESolver<?, ?, ? extends InterproceduralCFG<Unit, SootMethod>> analysis = executeStaticAnalysis(FunctionCall2.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair("i", 100));
        expected.add(new Pair("j", 200));
        expected.add(new Pair("k", 101));
        expected.add(new Pair("l", 201));
        checkResultsAtLastStatement(analysis, expected);
    }
}
