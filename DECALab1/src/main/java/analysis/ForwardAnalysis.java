package analysis;

import java.util.Map;

import soot.Body;
import soot.SootMethod;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.scalar.ForwardFlowAnalysis;
import soot.Unit;

public class ForwardAnalysis<F> extends ForwardFlowAnalysis<Unit, F> {
	protected VulnerabilityReporter reporter;
	protected SootMethod method;
		
	public ForwardAnalysis(Body body, VulnerabilityReporter reporter) {
		super(new ExceptionalUnitGraph(body));
		this.method = body.getMethod();
		this.reporter = reporter;
		System.out.println("Method: "+method.getSignature());
	}

	protected void prettyPrint(F in, Unit stmt, F out)
	{
		String s=String.format("\t%10s%s\n\t%10s%s\n\t%10s%s\n","In Fact: ",in.toString(),"Stmt: ",stmt.toString(),"Out Fact: ",out.toString());
		System.out.println(s); 
	}
	
	public Map<Unit,F> getUnitToAfterFlow()
	{
		return this.unitToAfterFlow;
	}
	
	@Override
	protected void flowThrough(F in, Unit stmt, F out) {
		// TODO Auto-generated method stub

	}

	@Override
	protected F newInitialFlow() {
		// TODO Auto-generated method ubst
		return null;
	}

	@Override
	protected void merge(F in1, F in2, F out) {
		// TODO Auto-generated method stub

	}

	@Override
	protected void copy(F source, F dest) {
		// TODO Auto-generated method stub

	}

	@Override
	public void doAnalysis() {
		super.doAnalysis();
	}
}
