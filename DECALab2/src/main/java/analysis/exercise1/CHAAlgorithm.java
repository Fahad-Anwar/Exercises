package analysis.exercise1;

import java.util.stream.Stream;

import analysis.CallGraph;
import analysis.CallGraphAlgorithm;
import soot.Body;
import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;

public class CHAAlgorithm extends CallGraphAlgorithm {

	@Override
	protected String getAlgorithm() {
		return "CHA";
	}

	@Override
	protected void populateCallGraph(Scene scene, CallGraph cg) {
		// Your implementation goes here, also feel free to add methods as needed
		// To get your entry points we prepared getEntryPoints(scene) in the superclass
		// for you
		Stream<SootMethod> entryPoints = getEntryPoints(scene);
		entryPoints.forEach(entryPoint -> {
//			 if (entryPoint.toString().equals("<target.exercise1.SimpleExample: void main(java.lang.String[])>")) {
				 checkMethod(null, entryPoint, cg, scene);
//			 }
		});

	}

	private void checkMethod(SootMethod src, SootMethod target, CallGraph cg, Scene scene) {

		addEdge(src, target, cg);

		if (target.hasActiveBody()) {
			Body b = target.getActiveBody();
			for (Unit u : b.getUnits()) {

				Stmt s = (Stmt) u;
				if (s.containsInvokeExpr()) {

					InvokeExpr expr = s.getInvokeExpr();
					checkMethod(target, expr.getMethod(), cg, scene);
				}

			}

		} else if (target.isAbstract()) {
			scene.getApplicationClasses().forEach(sampleClass -> {
				sampleClass.getInterfaces().forEach(impPhase -> {
					if (impPhase == target.getDeclaringClass()) {
						sampleClass.getMethods().forEach(method -> {
							if (method.getSubSignature().equals(target.getSubSignature())) {
								addEdge(src, method, cg);
								checkMethod(target, method, cg, scene);
							}
						});
					}
				});
			});

		}
	}

	private void addEdge(SootMethod src, SootMethod entryPoint, CallGraph cg) {
		if (!cg.hasNode(entryPoint))
			cg.addNode(entryPoint);
		if (src != null && !cg.hasNode(src))
			cg.addNode(src);
		if (src != null && !cg.hasEdge(src, entryPoint))
			cg.addEdge(src, entryPoint);
	}

}
