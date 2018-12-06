package test.exercises;

import org.junit.Before;
import org.junit.Test;

import analysis.VulnerabilityReporter;
import analysis.exercise.Exercise2FlowFunctions;
import target.exercise1.AssignmentSQLInjection;
import target.exercise1.DirectSQLInjection;
import target.exercise1.InterproceduralSQLInjection;
import target.exercise1.NoSQLInjection;
import target.exercise2and3.FieldNoSQLInjection;
import target.exercise2and3.FieldSQLInjection1;
import target.exercise2and3.FieldSQLInjection2;
import test.base.TestSetup;

public class Exercise2Test extends TestSetup{

	@Before
	public void setup(){
		reporter = new VulnerabilityReporter();
		flowFunctions = new Exercise2FlowFunctions(reporter);
	}
	
	@Test
	public void fieldSQLInjection1(){
		executeStaticAnalysis(FieldSQLInjection1.class.getName());
		
		//FIELDBASED represents a 
		assert containsDataFlowFactAtStmt("FIELDBASED <target.exercise2and3.FieldSQLInjection1$ObjectWithTaint: java.lang.String userInput>","conn = staticinvoke <java.sql.DriverManager: java.sql.Connection getConnection(java.lang.String,java.lang.String,java.lang.String)>(\"url\", \"userName\", \"password\")");
		assert containsDataFlowFactAtStmt("loaded","conn = staticinvoke <java.sql.DriverManager: java.sql.Connection getConnection(java.lang.String,java.lang.String,java.lang.String)>(\"url\", \"userName\", \"password\")");
		assert reporter.getReportedVulnerabilities() == 1;
	}
	@Test
	public void fieldSQLInjection2(){
		executeStaticAnalysis(FieldSQLInjection2.class.getName());
		
		assert containsDataFlowFactAtStmt("FIELDBASED <target.exercise2and3.FieldSQLInjection2$ObjectWithTaint: java.lang.String userInput>","conn = staticinvoke <java.sql.DriverManager: java.sql.Connection getConnection(java.lang.String,java.lang.String,java.lang.String)>(\"url\", \"userName\", \"password\")");
		assert containsDataFlowFactAtStmt("loaded","conn = staticinvoke <java.sql.DriverManager: java.sql.Connection getConnection(java.lang.String,java.lang.String,java.lang.String)>(\"url\", \"userName\", \"password\")");
		assert reporter.getReportedVulnerabilities() == 1;
	}

	@Test
	public void fieldBasedImpreciseTest(){
		executeStaticAnalysis(FieldNoSQLInjection.class.getName());
		
		assert containsDataFlowFactAtStmt("FIELDBASED <target.exercise2and3.FieldNoSQLInjection$ObjectWithTaint: java.lang.String userInput>","specialinvoke this.<target.exercise2and3.FieldNoSQLInjection: void createQuery(target.exercise2and3.FieldNoSQLInjection$ObjectWithTaint)>(o2)");
		assert containsDataFlowFactAtStmt("FIELDBASED <target.exercise2and3.FieldNoSQLInjection$ObjectWithTaint: java.lang.String userInput>","conn = staticinvoke <java.sql.DriverManager: java.sql.Connection getConnection(java.lang.String,java.lang.String,java.lang.String)>(\"url\", \"userName\", \"password\")");
		
		//This is an imprecise propagation
		assert containsDataFlowFactAtStmt("loaded","conn = staticinvoke <java.sql.DriverManager: java.sql.Connection getConnection(java.lang.String,java.lang.String,java.lang.String)>(\"url\", \"userName\", \"password\")");
		assert reporter.getReportedVulnerabilities() == 1;
	}
	

	// The analysis must still correctly detect the data flows from Exercise 1.
	@Test
	public void directSQLInjection(){
		executeStaticAnalysis(DirectSQLInjection.class.getName());
		
		//Checks that the return variable "userId" of the call to getParameter is tainted.
		assert containsDataFlowFactAtStmt("userId","conn = staticinvoke <java.sql.DriverManager: java.sql.Connection getConnection(java.lang.String,java.lang.String,java.lang.String)>(\"url\", \"userName\", \"password\")");

		assert containsDataFlowFactAtStmt("query","interfaceinvoke st.<java.sql.Statement: java.sql.ResultSet executeQuery(java.lang.String)>(query)");
		assert reporter.getReportedVulnerabilities() == 1;
	}

	@Test
	public void assignmentSQLInjection(){
		executeStaticAnalysis(AssignmentSQLInjection.class.getName());

		//Checks that the variable "alias" receives the taint as of the statement String alias = userId;
		assert containsDataFlowFactAtStmt("alias","conn = staticinvoke <java.sql.DriverManager: java.sql.Connection getConnection(java.lang.String,java.lang.String,java.lang.String)>(\"url\", \"userName\", \"password\")");
		
		assert containsDataFlowFactAtStmt("query","interfaceinvoke st.<java.sql.Statement: java.sql.ResultSet executeQuery(java.lang.String)>(query)");
		assert reporter.getReportedVulnerabilities() == 1;
	}

	@Test
	public void noSQLInjection(){
		executeStaticAnalysis(NoSQLInjection.class.getName());
		assert reporter.getReportedVulnerabilities() == 0;
	}
	
	@Test
	public void interproceduralSQLInjection(){
		executeStaticAnalysis(InterproceduralSQLInjection.class.getName());
		
		assert containsDataFlowFactAtStmt("userId","specialinvoke this.<target.exercise1.InterproceduralSQLInjection: void createQuery(java.lang.String)>(userId)");
		assert containsDataFlowFactAtStmt("parameter","conn = staticinvoke <java.sql.DriverManager: java.sql.Connection getConnection(java.lang.String,java.lang.String,java.lang.String)>(\"url\", \"userName\", \"password\")");
		
		assert reporter.getReportedVulnerabilities() == 1;
	}
}
