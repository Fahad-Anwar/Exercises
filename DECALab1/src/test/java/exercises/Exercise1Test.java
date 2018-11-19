package exercises;

import static org.junit.Assert.assertEquals;

import java.util.Map;

import org.junit.Test;

import analysis.VulnerabilityReporter;
import analysis.exercise1.MisuseAnalysis;
import base.TestSetup;
import soot.Body;
import soot.BodyTransformer;
import soot.Transformer;
import target.exercise1.Misuse;
import target.exercise1.NoMisuse;

public class Exercise1Test extends TestSetup {

	protected Transformer createAnalysisTransformer() {
		return new BodyTransformer() {

			@Override
			protected void internalTransform(Body body, String phaseName, Map<String, String> options) {
				MisuseAnalysis analysis = new MisuseAnalysis(body, reporter);
				analysis.doAnalysis();
			}
		};
	}

	@Test
	public void testMisuse() {
		reporter = new VulnerabilityReporter();
		executeStaticAnalysis(Misuse.class.getName());
		assertEquals(1, reporter.getReportedVulnerabilities().size());
		assertEquals("<target.exercise1.Misuse: void test()> - aesChipher = staticinvoke <javax.crypto.Cipher: javax.crypto.Cipher getInstance(java.lang.String)>(\"AES\")", reporter.getReportedVulnerabilities().get(0));		
	}
	@Test
	public void testNoMisuse() {
		reporter = new VulnerabilityReporter();
		executeStaticAnalysis(NoMisuse.class.getName());
		assertEquals(0, reporter.getReportedVulnerabilities().size());
	}
	
}
