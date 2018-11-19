package analysis.exercise2;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import analysis.FileState;
import analysis.FileStateFact;
import analysis.ForwardAnalysis;
import analysis.VulnerabilityReporter;
import soot.Body;
import soot.Unit;
import soot.Value;
import soot.jimple.Stmt;
import soot.jimple.internal.JReturnVoidStmt;

public class TypeStateAnalysis extends ForwardAnalysis<Set<FileStateFact>> {

	public TypeStateAnalysis(Body body, VulnerabilityReporter reporter) {
		super(body, reporter);
	}

	@Override
	protected void flowThrough(Set<FileStateFact> in, Unit unit, Set<FileStateFact> out) {
		copy(in, out);
		Stmt stmt = (Stmt) unit;
		if (stmt.containsInvokeExpr() || stmt.containsFieldRef()) {
			Value box1Value = unit.getUseAndDefBoxes().get(0).getValue();
			Value box2Value = unit.getUseAndDefBoxes().get(1).getValue();
			if (stmt.containsFieldRef()) {
				Iterator<FileStateFact> iterator = out.iterator();
				while (iterator.hasNext()) {
					FileStateFact next = iterator.next();
					if (next.containsAlias(box2Value)) {
						next.addAlias(box1Value);
					}
				}
			} else if (stmt.containsInvokeExpr()) {
				if (stmt.getInvokeExpr().getMethod().getSignature().equals("<target.exercise2.File: void <init>()>")) {
					Set<Value> values = new HashSet<Value>();
					values.add(box1Value);
					FileStateFact fileStateFact = new FileStateFact(values, FileState.Init);
					out.add(fileStateFact);
				} else if (stmt.getInvokeExpr().getMethod().getSignature()
						.equals("<target.exercise2.File: void open()>")
						|| (stmt.getInvokeExpr().getMethod().getSignature()
								.equals("<target.exercise2.File: void close()>"))) {
					Value base = stmt.getInvokeExpr().getUseBoxes().get(0).getValue();
					FileState fileState = stmt.getInvokeExpr().getMethod().getSignature()
							.equals("<target.exercise2.File: void open()>") ? FileState.Open : FileState.Close;
					Iterator<FileStateFact> iterator = out.iterator();
					while (iterator.hasNext()) {
						FileStateFact next = iterator.next();
						if (next.containsAlias(base)) {
							next.updateState(fileState);
						}
					}
				}

			}
		} else if (unit instanceof JReturnVoidStmt) {
			out.forEach(fileStateFact -> {
				if (fileStateFact.getState().equals(FileState.Open)
						|| fileStateFact.getState().equals(FileState.Init)) {
					reporter.reportVulnerability(method.getSignature(), unit);
				}
			});
		}
		prettyPrint(in, unit, out);
	}

	@Override
	protected Set<FileStateFact> newInitialFlow() {
		return new HashSet<FileStateFact>();
	}

	@Override
	protected void copy(Set<FileStateFact> source, Set<FileStateFact> dest) {
		for (FileStateFact fileStateFact : source) {
			dest.add(fileStateFact.copy());
		}
	}

	@Override
	protected void merge(Set<FileStateFact> in1, Set<FileStateFact> in2, Set<FileStateFact> out) {
		for (FileStateFact fileStateFact : in1) {
			out.add(fileStateFact.copy());
		}
		for (FileStateFact fileStateFact : in2) {
			out.add(fileStateFact.copy());
		}
	}

}
