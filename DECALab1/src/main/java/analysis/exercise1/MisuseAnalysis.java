package analysis.exercise1;

import analysis.AbstractAnalysis;
import analysis.VulnerabilityReporter;
import soot.Body;
import soot.SootMethodRef;
import soot.Unit;
import soot.Value;
import soot.jimple.InvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.internal.JAssignStmt;

public class MisuseAnalysis extends AbstractAnalysis{
	public MisuseAnalysis(Body body, VulnerabilityReporter reporter) {
		super(body, reporter);
	}
	
	@Override
	protected void flowThrough(Unit unit) {
		if (unit instanceof JAssignStmt) {
			Stmt stmt = (Stmt) unit;
			if (stmt.containsInvokeExpr()) {
				InvokeExpr invokeExpr = ((JAssignStmt) unit).getInvokeExpr();
				if (invokeExpr instanceof StaticInvokeExpr) {
					SootMethodRef sootMethodRef = invokeExpr.getMethodRef();
					if (sootMethodRef.getSubSignature().toString()
							.equals("javax.crypto.Cipher getInstance(java.lang.String)")) {
						Value arg = invokeExpr.getArg(0);
						if (((StringConstant) arg).value.equals("AES")) {
							this.reporter.reportVulnerability(this.method.toString(), unit);
						}
					}
				}
			}
		}
	}
}
