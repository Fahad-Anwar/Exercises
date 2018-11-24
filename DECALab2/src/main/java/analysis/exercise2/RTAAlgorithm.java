package analysis.exercise2;


import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Stream;

import analysis.CallGraph;
import analysis.exercise1.CHAAlgorithm;
import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;

public class RTAAlgorithm extends CHAAlgorithm  {

    @Override
    protected String getAlgorithm() {
        return "RTA";
    }

    @Override
    protected void populateCallGraph(Scene scene, CallGraph cg) {
        // Your implementation goes here, also feel free to add methods as needed
        // To get your entry points we prepared getEntryPoints(scene) in the superclass for you
    	Stream<SootMethod> entryPoints = getEntryPoints(scene);
		entryPoints.forEach(entryPoint -> {
			
			if (entryPoint.toString().equals("<target.exercise2.Starter: void main(java.lang.String[])>")) {
				Map<SootMethod, ArrayList<SootClass>> map = new HashMap<>();
				checkMethod(null, entryPoint, cg, scene, map);
			}
		});
    }

    private void checkMethod(SootMethod src, SootMethod entryPoint, CallGraph cg, Scene scene, Map<SootMethod, ArrayList<SootClass>> map) {
		// TODO Auto-generated method stub
		try {
			addEdge(src, entryPoint, cg);
			
						
			if (entryPoint.hasActiveBody()) {
				Body b = entryPoint.getActiveBody();
				for (Unit u : b.getUnits()) {

					Stmt s = (Stmt) u;
					if (s.containsInvokeExpr()) {
						InvokeExpr expr = s.getInvokeExpr();
						checkMethod(entryPoint, expr.getMethod(), cg, scene, map);
						if(expr.getMethod().isStatic() && !expr.getMethod().isJavaLibraryMethod()) {
							ArrayList<SootClass> classes;
							if(map.containsKey(entryPoint)) {
								classes = map.get(entryPoint);
							} else {
								classes = new ArrayList<SootClass>();
								map.put(entryPoint, classes);
							}
							cg.edgesOutOf(expr.getMethod()).stream().filter(e -> !e.isJavaLibraryMethod()).forEach( m -> {
								classes.add(m.getDeclaringClass());
							});
									
						}
					}

				}

			} else if (entryPoint.isAbstract() && !entryPoint.isJavaLibraryMethod()) {
				ArrayList<SootClass> list =	map.containsKey(src) ? map.get(src) : new ArrayList<>();
				scene.getApplicationClasses().stream().
				flatMap(c -> c.getMethods().stream()).
				filter(method -> method.getSubSignature().equals(entryPoint.getSubSignature())						
						&& method.getDeclaringClass() != entryPoint.getDeclaringClass()).forEach(m -> {
							if(list.contains(m.getDeclaringClass())) {
								addEdge(src, m, cg);
							}
						});

			}
		} catch (Exception e) {
			System.out.println("EXCEPTION:");
		} finally {
		}
	}

	private void addEdge(SootMethod src, SootMethod entryPoint, CallGraph cg) {
		if (!cg.hasNode(entryPoint)) cg.addNode(entryPoint);
		if (src != null && !cg.hasNode(src)) cg.addNode(src);
		if (src != null && !cg.hasEdge(src, entryPoint)) cg.addEdge(src, entryPoint);
	}
}
