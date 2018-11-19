package exercises;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.junit.Test;

import analysis.FileState;
import analysis.FileStateFact;
import analysis.VulnerabilityReporter;
import analysis.exercise2.TypeStateAnalysis;
import base.TestSetup;
import soot.Body;
import soot.BodyTransformer;
import soot.SootMethod;
import soot.Transformer;
import soot.Unit;
import soot.jimple.ReturnVoidStmt;
import target.exercise2.FileClosed;
import target.exercise2.FileClosedAliasing;
import target.exercise2.FileNotClosed;
import target.exercise2.FileNotClosedAliasing;

public class Exercise2Test extends TestSetup {
	private Map<SootMethod, Map<Unit, Set<FileStateFact>>> outFacts;

	protected Transformer createAnalysisTransformer() {
		return new BodyTransformer() {
			@Override
			protected void internalTransform(Body body, String phaseName, Map<String, String> options) {
				TypeStateAnalysis analysis = new TypeStateAnalysis(body, reporter);
				analysis.doAnalysis();
				outFacts.put(body.getMethod(), analysis.getUnitToAfterFlow());
			}
		};
	}

	@Test
	public void testFileClosed() {
		reporter = new VulnerabilityReporter();
		outFacts = new HashMap<>();
		executeStaticAnalysis(FileClosed.class.getName());
		assertEquals(0, reporter.getReportedVulnerabilities().size());
		// test selected out facts
		for (SootMethod method : outFacts.keySet()) {
			if (method.getSignature().equals("<target.exercise2.FileClosed: void test1()>")) {
				Map<Unit, Set<FileStateFact>> result = outFacts.get(method);
				for (Unit unit : result.keySet()) {
					if (unit.toString().equals("specialinvoke $r0.<target.exercise2.File: void <init>()>()")) {
						assertEquals("[([$r0], Init)]", result.get(unit).toString());
					}
					if (unit instanceof ReturnVoidStmt) {
						assertEquals("[([$r0], Close)]", result.get(unit).toString());
					}
				}
			}
			if (method.getSignature().equals("<target.exercise2.FileClosed: void test2()>")) {
				Map<Unit, Set<FileStateFact>> result = outFacts.get(method);
				for (Unit unit : result.keySet()) {
					if (unit.toString().equals("virtualinvoke $r0.<target.exercise2.File: void open()>()")) {
						assertEquals("[([$r0], Open)]", result.get(unit).toString());

					}
					if (unit instanceof ReturnVoidStmt) {
						assertEquals("[([$r0], Close)]", result.get(unit).toString());
					}
				}
			}
		}
	}

	@Test
	public void testFileClosedAliasing() {
		reporter = new VulnerabilityReporter();
		outFacts = new HashMap<>();
		executeStaticAnalysis(FileClosedAliasing.class.getName());
		assertEquals(0, reporter.getReportedVulnerabilities().size());
		// test selected out facts
		for (SootMethod method : outFacts.keySet()) {
			if (method.getSignature().equals("<target.exercise2.FileClosedAliasing: void test1()>")) {
				Map<Unit, Set<FileStateFact>> result = outFacts.get(method);
				for (Unit unit : result.keySet()) {
					if (unit.toString().equals("virtualinvoke $r0.<target.exercise2.File: void open()>()")) {
						assertEquals("[([$r0], Open)]", result.get(unit).toString());

					}
					if (unit instanceof ReturnVoidStmt) {
						assertEquals("[([$r0], Close)]", result.get(unit).toString());
					}
				}
			}
			if (method.getSignature().equals("<target.exercise2.FileClosedAliasing: void test2()>")) {
				Map<Unit, Set<FileStateFact>> result = outFacts.get(method);
				for (Unit unit : result.keySet()) {
					if (unit.toString().equals("virtualinvoke $r1.<target.exercise2.File: void open()>()")) {
						assertEquals(result.get(unit).iterator().next().getState(), FileState.Open);
					}
					if (unit instanceof ReturnVoidStmt) {
						FileStateFact fact = result.get(unit).iterator().next();
						assertTrue(fact.containsAlias("file"));
						assertEquals(fact.getState(), FileState.Close);
					}
				}
			}
		}
	}

	@Test
	public void testFileNotClosed() {
		reporter = new VulnerabilityReporter();
		outFacts = new HashMap<>();
		executeStaticAnalysis(FileNotClosed.class.getName());
		assertEquals(3, reporter.getReportedVulnerabilities().size());
		// test selected out facts
		for (SootMethod method : outFacts.keySet()) {
			if (method.getSignature().equals("<target.exercise2.FileNotClosed: void test1()>")) {
				Map<Unit, Set<FileStateFact>> result = outFacts.get(method);
				for (Unit unit : result.keySet()) {
					if (unit instanceof ReturnVoidStmt) {
						assertEquals("[([$r0], Open)]", result.get(unit).toString());
					}
				}
			}
			if (method.getSignature().equals("<target.exercise2.FileNotClosed: void test2()>")) {
				Map<Unit, Set<FileStateFact>> result = outFacts.get(method);
				for (Unit unit : result.keySet()) {
					if (unit instanceof ReturnVoidStmt) {
						boolean containsOpen = false;
						for (FileStateFact f : result.get(unit)) {
							if (f.getState().equals(FileState.Open))
								containsOpen = true;
						}
						assertTrue(containsOpen);
					}
				}
			}
			if (method.getSignature().equals("<target.exercise2.FileNotClosed: void test3()>")) {
				Map<Unit, Set<FileStateFact>> result = outFacts.get(method);
				for (Unit unit : result.keySet()) {
					if (unit instanceof ReturnVoidStmt) {
						boolean containsOpen = false;
						for (FileStateFact f : result.get(unit)) {
							if (f.getState().equals(FileState.Open))
								containsOpen = true;
						}
						assertTrue(containsOpen);
					}
				}
			}
		}
	}

	@Test
	public void testFileNotClosedAliasing() {
		reporter = new VulnerabilityReporter();
		outFacts = new HashMap<>();
		executeStaticAnalysis(FileNotClosedAliasing.class.getName());
		assertEquals(4, reporter.getReportedVulnerabilities().size());
		// test selected out facts
		for (SootMethod method : outFacts.keySet()) {
			if (method.getSignature().equals("<target.exercise2.FileNotClosedAliasing: void test2()>")) {
				Map<Unit, Set<FileStateFact>> result = outFacts.get(method);
				for (Unit unit : result.keySet()) {
					if (unit instanceof ReturnVoidStmt) {
						FileStateFact fact = result.get(unit).iterator().next();
						assertTrue(fact.containsAlias(
								"<target.exercise2.FileNotClosedAliasing: target.exercise2.File staticFile>"));
						assertEquals(fact.getState(), FileState.Open);
					}
				}
			}
		}
	}

}
