package analysis;

import soot.Body;
import soot.SootMethod;
import soot.Unit;

public abstract class AbstractAnalysis {

	protected VulnerabilityReporter reporter;
	protected Body body;
	protected SootMethod method;

	protected AbstractAnalysis(Body body, VulnerabilityReporter reporter) {
		this.body = body;
		this.reporter = reporter;
		this.method = body.getMethod();
	}

	protected abstract void flowThrough(Unit unit);

	public void doAnalysis() {
		for (Unit unit : this.body.getUnits()) {
			flowThrough(unit);
		}
	}
}
