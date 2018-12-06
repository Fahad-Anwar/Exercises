package test.exercises;

import org.junit.Before;
import org.junit.Test;

import analysis.VulnerabilityReporter;
import analysis.exercise.Exercise3FlowFunctions;
import target.exercise4.UnsoundExample;
import test.base.TestSetup;

public class Exercise4Test extends TestSetup {

	@Before
	public void setup() {
		reporter = new VulnerabilityReporter();
		//Use flow function created for Exercise 3.
		flowFunctions = new Exercise3FlowFunctions(reporter);
	}
	
	@Test
	public void unsoundExample(){
		executeStaticAnalysis(UnsoundExample.class.getName());
		//The analysis must not detect a data-flow here, even though there is one.
		assert reporter.getReportedVulnerabilities() == 0;
	}
}
