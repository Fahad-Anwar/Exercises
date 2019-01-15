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
import soot.jimple.internal.JimpleLocal;

public class Exercise3FlowFunctions extends TaintAnalysisFlowFunctions {

	private VulnerabilityReporter reporter;

	public Exercise3FlowFunctions(VulnerabilityReporter reporter) {
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
				//TODO: Implement interprocedural part of Exercise 3 here.
				if (callSiteStmt instanceof JInvokeStmt && callSiteStmt.containsInvokeExpr()) {
					InvokeStmt invokeStmt = ((InvokeStmt) callSiteStmt);
					int total_num_args = invokeStmt.getInvokeExpr().getArgCount();
					List<Value> arguments = invokeStmt.getInvokeExpr().getArgs();
					List<Local> parameterLocals = callee.getActiveBody().getParameterLocals();
					for (int index = 0; index < total_num_args; index++) {
						if (index < parameterLocals.size() && fact.getVariable().equals(arguments.get(index))) {
							out.add(new DataFlowFact(parameterLocals.get(index), fact.getField()));
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
				Stmt callSiteStatementt = (Stmt) curr;
				if (callSiteStatementt instanceof AssignStmt) {
					Value leftOp = ((JAssignStmt) callSiteStatementt).getLeftOp();
					Value rightOp = ((JAssignStmt) callSiteStatementt).getRightOp();
					if (leftOp instanceof Local
							&& rightOp.toString().contains("java.lang.String getParameter(java.lang.String)")) {
							out.add(new DataFlowFact((Local) leftOp));
					}
				}
				//TODO: Implement cases for field load and field store statement of Exercise 3) here
				if (callSiteStatementt instanceof AssignStmt) {
					AssignStmt assingStmt = (AssignStmt)callSiteStatementt;
					Value leftOpValue = assingStmt.getLeftOp();
					Value rightOpValue = assingStmt.getRightOp();
					if (rightOpValue instanceof JimpleLocal && fact.getVariable().equals((JimpleLocal)rightOpValue)) {
						if(leftOpValue instanceof JimpleLocal) { 
							out.add(new DataFlowFact((JimpleLocal) leftOpValue));
						} else if (leftOpValue instanceof FieldRef && leftOpValue.getUseBoxes().size() == 1) {
							Value v = leftOpValue.getUseBoxes().get(0).getValue();
							if (v instanceof JimpleLocal) {
								out.add(new DataFlowFact((Local) v, ((FieldRef) leftOpValue).getField()));
							}
						}
					} else if (rightOpValue instanceof FieldRef && rightOpValue.getUseBoxes().size() == 1) {
						Value v = rightOpValue.getUseBoxes().get(0).getValue();
						if (v instanceof JimpleLocal && fact.getVariable().equals(v)) {
							out.add(new DataFlowFact((JimpleLocal) leftOpValue));
						}
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
