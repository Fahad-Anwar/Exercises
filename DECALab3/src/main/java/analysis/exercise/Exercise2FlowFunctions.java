package analysis.exercise;

import java.util.Collections;
import java.util.List;
import java.util.Set;

import com.google.common.collect.Sets;

import analysis.TaintAnalysisFlowFunctions;
import analysis.VulnerabilityReporter;
import analysis.fact.DataFlowFact;
import heros.FlowFunction;
import soot.Local;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.FieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.Stmt;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInvokeStmt;

public class Exercise2FlowFunctions extends TaintAnalysisFlowFunctions {

	private VulnerabilityReporter reporter;

	public Exercise2FlowFunctions(VulnerabilityReporter reporter) {
		this.reporter = reporter;
	}

	@Override
	public FlowFunction<DataFlowFact> getCallFlowFunction(Unit callSite, SootMethod callee) {
		return new FlowFunction<DataFlowFact>() {
			@Override
			public Set<DataFlowFact> computeTargets(DataFlowFact fact) {
				if(fact.equals(DataFlowFact.zero()))
					return Collections.emptySet();
				prettyPrint(callSite, fact);
				Set<DataFlowFact> out = Sets.newHashSet();
				if(!(callSite instanceof Stmt)){
					return out;
				}
				Stmt callSiteStmt = (Stmt) callSite;
				//TODO: Implement Exercise 1c) here
				if (callSiteStmt instanceof JInvokeStmt && callSiteStmt.containsInvokeExpr()) {
					InvokeStmt invokeStatement = ((InvokeStmt) callSiteStmt);
					int total_num_args = invokeStatement.getInvokeExpr().getArgCount();
					List<Value> arguments = invokeStatement.getInvokeExpr().getArgs();
					List<Local> parameterLocals = callee.getActiveBody().getParameterLocals();
					for (int index = 0; index < total_num_args; index++) {
						if (index < parameterLocals.size() && fact.getVariable().equals(arguments.get(index))) {
							out.add(new DataFlowFact(parameterLocals.get(index)));
						}
					}

				}
				//TODO: Implement interprocedural part of Exercise 2 here
				if (callSiteStmt instanceof AssignStmt) {
					Value leftOpValue = ((JAssignStmt) callSiteStmt).getLeftOp();
					Value rightOpValue = ((JAssignStmt) callSiteStmt).getRightOp();
					if (fact.getVariable().equals(rightOpValue)) {
						if (leftOpValue instanceof Local) {
							out.add(new DataFlowFact((Local) leftOpValue));
						}
					} 
				}
				return out;
			}
		};
	}

	public FlowFunction<DataFlowFact> getCallToReturnFlowFunction(final Unit call, Unit returnSite) {
		return new FlowFunction<DataFlowFact>() {

			@Override
			public Set<DataFlowFact> computeTargets(DataFlowFact val) {

				Set<DataFlowFact> out = Sets.newHashSet();
				Stmt callSiteStmt = (Stmt) call;
				out.add(val);
				modelStringOperations(val, out, callSiteStmt);
				
				if(val.equals(DataFlowFact.zero())){
					//TODO: Implement Exercise 1a) here
					if (callSiteStmt instanceof AssignStmt) {
						Value leftOpValue = ((JAssignStmt) callSiteStmt).getLeftOp();
						Value rightOpValue = ((JAssignStmt) callSiteStmt).getRightOp();
						if (leftOpValue instanceof Local
								&& rightOpValue.toString().contains("java.lang.String getParameter(java.lang.String)")) {
								out.add(new DataFlowFact((Local) leftOpValue));
						}
					}
				}
				if(call instanceof Stmt && call.toString().contains("executeQuery")){
					Stmt stmt = (Stmt) call;
					Value arg = stmt.getInvokeExpr().getArg(0);
					if(val.getVariable().equals(arg)){
						reporter.reportVulnerability();
					}
				}
				return out;
			}
		};
	}
	private void modelStringOperations(DataFlowFact fact, Set<DataFlowFact> out,
			Stmt callSiteStmt) {
		if(callSiteStmt instanceof AssignStmt && callSiteStmt.toString().contains("java.lang.StringBuilder append(") && callSiteStmt.getInvokeExpr() instanceof InstanceInvokeExpr){
			Value arg0 = callSiteStmt.getInvokeExpr().getArg(0);
			Value base = ((InstanceInvokeExpr) callSiteStmt.getInvokeExpr()).getBase();
			/*Does the propagated value match the first parameter of the append call or the base variable*/
			if(fact.getVariable().equals(arg0) || fact.getVariable().equals(base)){ 
				/*Yes, then taint the left side of the assignment*/
				Value leftOp = ((AssignStmt) callSiteStmt).getLeftOp();
				if(leftOp instanceof Local){
					out.add(new DataFlowFact((Local) leftOp));
				}
			}
		}
		

		/*For any call x = var.toString(), if the base variable var is tainted, then x is tainted.*/
		if(callSiteStmt instanceof AssignStmt && callSiteStmt.toString().contains("toString()")){
			if(callSiteStmt.getInvokeExpr() instanceof InstanceInvokeExpr){
				InstanceInvokeExpr instanceInvokeExpr = (InstanceInvokeExpr) callSiteStmt.getInvokeExpr();
				if(fact.getVariable().equals(instanceInvokeExpr.getBase())){
					Value leftOp = ((AssignStmt) callSiteStmt).getLeftOp();
					if(leftOp instanceof Local){
						out.add(new DataFlowFact((Local) leftOp));
					}
				}
			}
		}
	}
	@Override
	public FlowFunction<DataFlowFact> getNormalFlowFunction(final Unit curr, Unit succ) {
		return new FlowFunction<DataFlowFact>() {
			@Override
			public Set<DataFlowFact> computeTargets(DataFlowFact fact) {
				prettyPrint(curr, fact);
				Set<DataFlowFact> out = Sets.newHashSet();
				out.add(fact);

				//TODO: Implement Exercise 1a) here
				Stmt statement = (Stmt) curr;
				if (statement instanceof JAssignStmt) {
					Value leftOpValue = ((JAssignStmt) statement).getLeftOp();
					Value rightOpValue = ((JAssignStmt) statement).getRightOp();
					if (leftOpValue instanceof Local && rightOpValue instanceof FieldRef) {						
                        out.add(new DataFlowFact((Local) leftOpValue));
					}
				}
				
				//TODO: Implement cases for field load and field store statement of Exercise 2) here
				if (curr instanceof AssignStmt) {
					Value leftOpValue = ((JAssignStmt) statement).getLeftOp();
					Value rightOpValue = ((JAssignStmt) statement).getRightOp();
					if (fact.getVariable().equals(rightOpValue)) {
						if (leftOpValue instanceof Local) {
							out.add(new DataFlowFact((Local) leftOpValue));
						}
					} else if (rightOpValue instanceof FieldRef) {
                        FieldRef right = (FieldRef) rightOpValue;
                        out.add(new DataFlowFact(right.getField()));
                    } else if (leftOpValue instanceof FieldRef) {
                        FieldRef left = (FieldRef) leftOpValue;
                        out.add(new DataFlowFact(left.getField()));
                    }
				}				
				return out;
			}
		};
	}

	@Override
	public FlowFunction<DataFlowFact> getReturnFlowFunction(Unit callSite, SootMethod callee, Unit exitStmt, Unit retSite) {
		return new FlowFunction<DataFlowFact>() {
			@Override
			public Set<DataFlowFact> computeTargets(DataFlowFact fact) {
				prettyPrint(callSite, fact);
				return Collections.emptySet();
			}
		};
	}
	
}
