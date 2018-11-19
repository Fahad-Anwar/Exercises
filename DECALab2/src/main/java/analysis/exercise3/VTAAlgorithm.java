package analysis.exercise3;

import analysis.CallGraph;
import analysis.CallGraphAlgorithm;
import analysis.exercise1.CHAAlgorithm;
import soot.*;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JInvokeStmt;

import java.util.HashSet;
import java.util.Set;

public class VTAAlgorithm extends CallGraphAlgorithm {

     

    @Override
    protected String getAlgorithm() {
        return "VTA";
    }

    @Override
    protected void populateCallGraph(Scene scene, CallGraph cg) {
         CallGraph initialCallGraph = new CHAAlgorithm().constructCallGraph(scene);

        // Your implementation goes here, also feel free to add methods as needed
        // To get your entry points we prepared getEntryPoints(scene) in the superclass for you

        
        getEntryPoints(scene).forEach(entryPoint -> {
            if(entryPoint.toString().equals("<target.exercise3.SimpleScenario: void main(java.lang.String[])>")) {
                cg.addNode(entryPoint.method());
                Set<SootClass> initiated = new HashSet<SootClass>();
                parseMethodBody(scene, cg, entryPoint ,initiated);
            }
        });

    }

    private void parseMethodBody(Scene scene, CallGraph cg, SootMethod currentMethod, Set<SootClass> initializedClasses) {
       
        currentMethod.getActiveBody().getUnits().forEach(unit -> {
            
            SootMethod nextMethod = getNextMethod(unit, scene);
            
            if (nextMethod != null) {
                if (!nextMethod.isAbstract()) {
                    if(!cg.hasNode(nextMethod)) {
                        cg.addNode(nextMethod);
                    }

                    if(!cg.hasEdge(currentMethod, nextMethod)) {
                        cg.addEdge(currentMethod, nextMethod);
                    }
                    
                    
                }

                if (nextMethod.hasActiveBody() && !nextMethod.isJavaLibraryMethod() && !nextMethod.isConstructor()) {
                    parseMethodBody(scene, cg, nextMethod, initializedClasses);
                }

                if (!nextMethod.isJavaLibraryMethod() && nextMethod.isConstructor()) {
                    initializedClasses.add(nextMethod.getDeclaringClass());
                }

                if (nextMethod.isAbstract()) {
                    scene.getApplicationClasses().forEach(nextClass -> {
                        if (isChild(nextClass, nextMethod.getDeclaringClass()) && initializedClasses.contains(nextClass)) {
                            SootMethod method = nextClass.getMethod(nextMethod.getSubSignature());

                            if(!cg.hasNode(method)) {
                                cg.addNode(method);
                            }

                            if(!cg.hasEdge(currentMethod, method)) {
                                cg.addEdge(currentMethod, method);
                            }
                            
                            if (!method.isConstructor() && method.hasActiveBody() && !method.isJavaLibraryMethod()) {
                                parseMethodBody(scene, cg, method, initializedClasses);
                            }
                        };
                    });
                }
            }
        });
    }


    private SootMethod getNextMethod(Unit unit, Scene scene) {
         if(unit instanceof JInvokeStmt) {
         	return scene.getMethod(((JInvokeStmt) unit).getInvokeExpr().getMethod().toString());
         } else if((unit instanceof JAssignStmt && ((JAssignStmt) unit).containsInvokeExpr())) {
          	return scene.getMethod(((JAssignStmt) unit).getInvokeExpr().getMethod().toString());
          } 
         return null;
	}

	private boolean isChild(SootClass descendent, SootClass ancestor) {
        if (descendent.getSuperclass() == ancestor) return true;
        
        for (SootClass implementedInterface : descendent.getInterfaces()) {
            if (implementedInterface == ancestor) {
                return true;
            }
        }

        if (descendent.getSuperclass().getName().equals("java.lang.Object")) return false;

        return isChild(descendent.getSuperclass(), ancestor);
    }


}