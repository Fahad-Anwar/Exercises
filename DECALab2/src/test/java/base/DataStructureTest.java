package base;

import analysis.CallGraph;
import analysis.Edge;
import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import soot.BooleanType;
import soot.SootClass;
import soot.SootMethod;

import java.util.Set;

public class DataStructureTest {
    @Test
    public void edgeEquality() {
        SootMethod source = new SootMethod("sourceMethod", null, BooleanType.v());
        SootMethod target = new SootMethod("targetMethod", null, BooleanType.v());
        SootClass testClass = new SootClass("TestClass");
        testClass.addMethod(source);
        testClass.addMethod(target);

        Assert.assertNotEquals(source, target);

        Edge<SootMethod, SootMethod> edge = new Edge<>(source, target);

        Assert.assertEquals("(" + edge.source.toString() + " --> " + edge.target.toString() + ")", edge.toString());

        Edge<SootMethod, SootMethod> sameEdge = new Edge<>(source, target);
        Edge<SootMethod, SootMethod> anotherEdge = new Edge<>(target, source);

        Assert.assertEquals(sameEdge, edge);
        Assert.assertEquals(sameEdge.hashCode(), edge.hashCode());

        Assert.assertNotEquals(anotherEdge, edge);
        Assert.assertNotEquals(anotherEdge.hashCode(), edge.hashCode());
    }

    @Rule
    public ExpectedException thrown = ExpectedException.none();

    @Test
    public void callGraphDoubleNode() {
        SootMethod source = new SootMethod("sourceMethod", null, BooleanType.v());
        SootClass testClass = new SootClass("TestClass");
        testClass.addMethod(source);

        CallGraph testCG = new CallGraph("Test");
        Assert.assertEquals("Test",testCG.algorithm);

        thrown.expect(IllegalArgumentException.class);

        testCG.addNode(source);
        testCG.addNode(source);
    }

    @Test
    public void callGraphDoubleEdge() {
        SootMethod source = new SootMethod("sourceMethod", null, BooleanType.v());
        SootMethod target = new SootMethod("targetMethod", null, BooleanType.v());
        SootClass testClass = new SootClass("TestClass");
        testClass.addMethod(source);
        testClass.addMethod(target);

        CallGraph testCG = new CallGraph("Test");
        Assert.assertEquals("Test",testCG.algorithm);

        thrown.expect(IllegalArgumentException.class);

        testCG.addNode(source);
        testCG.addNode(target);
        testCG.addEdge(source, target);
        testCG.addEdge(source, target);
    }

    @Test
    public void callGraphUnknownNode() {
        SootMethod source = new SootMethod("sourceMethod", null, BooleanType.v());
        SootMethod target = new SootMethod("targetMethod", null, BooleanType.v());
        SootClass testClass = new SootClass("TestClass");
        testClass.addMethod(source);
        testClass.addMethod(target);

        SootMethod firstMethod = new SootMethod("firstMethod", null, BooleanType.v());
        SootMethod secondMethod = new SootMethod("secondMethod", null, BooleanType.v());
        SootClass anotherClass = new SootClass("AnotherClass");
        anotherClass.addMethod(firstMethod);
        anotherClass.addMethod(secondMethod);

        CallGraph testCG = new CallGraph("Test");
        Assert.assertEquals("Test",testCG.algorithm);

        thrown.expect(IllegalArgumentException.class);

        testCG.addNode(source);
        testCG.addNode(target);
        testCG.addEdge(source, target);
        testCG.addEdge(source, firstMethod);
    }

    @Test
    public void callGraphValidScenario() {
        SootMethod source = new SootMethod("sourceMethod", null, BooleanType.v());
        SootMethod target = new SootMethod("targetMethod", null, BooleanType.v());
        SootClass testClass = new SootClass("TestClass");
        testClass.addMethod(source);
        testClass.addMethod(target);

        SootMethod firstMethod = new SootMethod("firstMethod", null, BooleanType.v());
        SootMethod secondMethod = new SootMethod("secondMethod", null, BooleanType.v());
        SootClass anotherClass = new SootClass("AnotherClass");
        anotherClass.addMethod(firstMethod);
        anotherClass.addMethod(secondMethod);

        CallGraph testCG = new CallGraph("Test");
        Assert.assertEquals("Test",testCG.algorithm);

        testCG.addNode(source);
        testCG.addNode(target);
        testCG.addNode(firstMethod);
        testCG.addNode(secondMethod);
        testCG.addEdge(source, target);
        testCG.addEdge(source, firstMethod);
        testCG.addEdge(target, firstMethod);
        testCG.addEdge(firstMethod, secondMethod);

        Assert.assertTrue(testCG.hasNode(source));
        Assert.assertTrue(testCG.hasNode(target));
        Assert.assertTrue(testCG.hasNode(firstMethod));
        Assert.assertTrue(testCG.hasNode(secondMethod));

        Assert.assertTrue(testCG.hasEdge(source, target));
        Assert.assertTrue(testCG.hasEdge(source, firstMethod));
        Assert.assertTrue(testCG.hasEdge(target, firstMethod));
        Assert.assertTrue(testCG.hasEdge(firstMethod, secondMethod));

        Set<SootMethod> eIntoSource = testCG.edgesInto(source);
        Set<SootMethod> eIntoTarget = testCG.edgesInto(target);
        Set<SootMethod> eIntoFirst = testCG.edgesInto(firstMethod);
        Set<SootMethod> eIntoSecond = testCG.edgesInto(secondMethod);

        Set<SootMethod> eOutOfSource = testCG.edgesOutOf(source);
        Set<SootMethod> eOutOfTarget = testCG.edgesOutOf(target);
        Set<SootMethod> eOutOfFirst = testCG.edgesOutOf(firstMethod);
        Set<SootMethod> eOutOfSecond = testCG.edgesOutOf(secondMethod);

        Assert.assertEquals(0, eIntoSource.size());
        Assert.assertEquals(2, eOutOfSource.size());
        Assert.assertEquals(1, eIntoTarget.size());
        Assert.assertEquals(1, eOutOfTarget.size());
        Assert.assertEquals(2, eIntoFirst.size());
        Assert.assertEquals(1, eOutOfFirst.size());
        Assert.assertEquals(1, eIntoSecond.size());
        Assert.assertEquals(0, eOutOfSecond.size());

        Assert.assertTrue(eOutOfSource.contains(target));
        Assert.assertTrue(eOutOfSource.contains(firstMethod));
        Assert.assertArrayEquals(new SootMethod[] {source}, eIntoTarget.toArray());
        Assert.assertArrayEquals(new SootMethod[] {firstMethod}, eOutOfTarget.toArray());
        Assert.assertTrue(eIntoFirst.contains(target));
        Assert.assertTrue(eIntoFirst.contains(source));
        Assert.assertArrayEquals(new SootMethod[] {secondMethod}, eOutOfFirst.toArray());
        Assert.assertArrayEquals(new SootMethod[] {firstMethod}, eIntoSecond.toArray());
    }
}
