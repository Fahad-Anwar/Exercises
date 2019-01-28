package test.exercises;

import heros.InterproceduralCFG;
import heros.solver.Pair;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import static org.junit.Assert.fail;
import org.junit.Test;
import soot.Local;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.toolkits.ide.JimpleIFDSSolver;

import target.exercise1and2.Branching;
import target.exercise1and2.Branching2;
import target.exercise1and2.FunctionCall;
import target.exercise1and2.FunctionCall2;
import target.exercise1and2.FunctionCall3;
import target.exercise1and2.Loop;
import target.exercise1and2.Loop2;
import target.exercise1and2.SimpleAssignment;
import target.exercise1and2.SimpleAssignment2;
import target.exercise1and2.SimpleAssignment3;
import target.exercise1and2.SimpleAssignment4;
import target.exercise1and2.SimpleAssignment5;
import test.base.IFDSTestSetUp;

public class Exercise1Test extends IFDSTestSetUp {

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

    void checkResultsAtLastStatement(JimpleIFDSSolver<?, InterproceduralCFG<Unit, SootMethod>> analysis, List<Pair<String, Integer>> expectedResult) {
        SootMethod m = getEntryPointMethod();
        Set<?> res = analysis.ifdsResultsAt(m.getActiveBody().getUnits().getLast());
        int correctResultCounter = 0;
        for (Pair<String, Integer> expected : expectedResult) {
            for (Pair<Local, Integer> actual : (Set<Pair<Local, Integer>>) res) {
                if (expected.getO1().equals(actual.getO1().getName()) && expected.getO2().intValue() == actual.getO2().intValue()) {
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
        JimpleIFDSSolver<?, InterproceduralCFG<Unit, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair("i", 100));
        expected.add(new Pair("j", 200));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void SimpleAssignment2() {
        JimpleIFDSSolver<?, InterproceduralCFG<Unit, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment2.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair("i", 100));
        expected.add(new Pair("j", 200));
        expected.add(new Pair("k", 40));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void SimpleAssignment3() {
        JimpleIFDSSolver<?, InterproceduralCFG<Unit, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment3.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair("i", 100));
        expected.add(new Pair("j", 200));
        expected.add(new Pair("k", 400));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void SimpleAssignment4() {
        JimpleIFDSSolver<?, InterproceduralCFG<Unit, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment4.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair("i", 100));
        expected.add(new Pair("j", 200));
        expected.add(new Pair("k", 413));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void SimpleAssignment5() {
        JimpleIFDSSolver<?, InterproceduralCFG<Unit, SootMethod>> analysis = executeStaticAnalysis(SimpleAssignment5.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair("j", 200));
        expected.add(new Pair("i", 13));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void Branching() {
        JimpleIFDSSolver<?, InterproceduralCFG<Unit, SootMethod>> analysis = executeStaticAnalysis(Branching.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair("i", 0));
        expected.add(new Pair("i#2", 10));
        expected.add(new Pair("j", 1));
        expected.add(new Pair("k", 14));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void Branching2() {
        JimpleIFDSSolver<?, InterproceduralCFG<Unit, SootMethod>> analysis = executeStaticAnalysis(Branching2.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair("i", 0));
        expected.add(new Pair("j", 0));
        expected.add(new Pair("j#2", 42));
        expected.add(new Pair("k", 13));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void Loop() {
        JimpleIFDSSolver<?, InterproceduralCFG<Unit, SootMethod>> analysis = executeStaticAnalysis(Loop.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair("sum", 1000));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void Loop2() {
        JimpleIFDSSolver<?, InterproceduralCFG<Unit, SootMethod>> analysis = executeStaticAnalysis(Loop2.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair("sum", 1000));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void FunctionCall() {
        JimpleIFDSSolver<?, InterproceduralCFG<Unit, SootMethod>> analysis = executeStaticAnalysis(FunctionCall.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair("i", 100));
        expected.add(new Pair("j", 200));
        expected.add(new Pair("k", 300));
        expected.add(new Pair("l", 400));
        checkResultsAtLastStatement(analysis, expected);
    }

    @Test
    public void FunctionCall2() {
        JimpleIFDSSolver<?, InterproceduralCFG<Unit, SootMethod>> analysis = executeStaticAnalysis(FunctionCall2.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair("i", 100));
        expected.add(new Pair("j", 200));
        expected.add(new Pair("k", 101));
        expected.add(new Pair("l", 201));
        checkResultsAtLastStatement(analysis, expected);
    }
//

    @Test
    public void FunctionCall3() {
        JimpleIFDSSolver<?, InterproceduralCFG<Unit, SootMethod>> analysis = executeStaticAnalysis(FunctionCall3.class.getName());
        List<Pair<String, Integer>> expected = new ArrayList<>();
        expected.add(new Pair("i", 100));
        expected.add(new Pair("j", 200));
        expected.add(new Pair("k", 113));
        expected.add(new Pair("l", 55));
        checkResultsAtLastStatement(analysis, expected);
    }

}
