package analysis.exercise3;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import org.graphstream.algorithm.TarjanStronglyConnectedComponents;
import org.graphstream.graph.Edge;
import org.graphstream.graph.Graph;
import org.graphstream.graph.Node;
import org.graphstream.graph.implementations.MultiGraph;
import org.objectweb.asm.tree.analysis.SourceInterpreter;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import analysis.CallGraph;
import analysis.CallGraphAlgorithm;
import analysis.exercise1.CHAAlgorithm;
import soot.PatchingChain;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.FieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JCastExpr;
import soot.jimple.internal.JInterfaceInvokeExpr;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JVirtualInvokeExpr;

public class VTAAlgorithm extends CallGraphAlgorithm {

    private final Logger log = LoggerFactory.getLogger("VTA");

    @Override
    protected String getAlgorithm() {
        return "VTA";
    }

    @Override
    protected void populateCallGraph(Scene scene, CallGraph cg) {
    	CallGraph initialCallGraph = new CHAAlgorithm().constructCallGraph(scene);

        // Your implementation goes here, also feel free to add methods as needed
        // To get your entry points we prepared getEntryPoints(scene) in the superclass for you
    	
    	TypeAssignmentGraph typeAssignmentGraph = new TypeAssignmentGraph();
        getEntryPoints(scene).forEach(entryPoint -> {
            if(entryPoint.toString().equals("<target.exercise3.SimpleScenario: void main(java.lang.String[])>")) {
                cg.addNode(entryPoint.method());                
                parseMethodBody(scene, cg, entryPoint, typeAssignmentGraph, initialCallGraph);
                
            }
        });
       
    }

    private void parseMethodBody(Scene scene, CallGraph cg, SootMethod currentMethod, TypeAssignmentGraph typeAssignmentGraph, CallGraph initialCallGraph) {
        
        PatchingChain<Unit> units = currentMethod.getActiveBody().getUnits();
        for (Unit unit : units) {

            SootMethod nextMethod = getNextMethod(unit, typeAssignmentGraph, initialCallGraph);
            
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
                    parseMethodBody(scene, cg, nextMethod, typeAssignmentGraph, initialCallGraph);
                }

				if (nextMethod.isAbstract()) {
					Value target;
					Stmt stmt = (Stmt) unit;
					InvokeExpr invokeExpr = stmt.getInvokeExpr();
					target = ((JInterfaceInvokeExpr) invokeExpr).getBaseBox().getValue();
					
					Set<SootClass> taggedClasses = typeAssignmentGraph.getNodeTags(target);
					for (SootClass sc : taggedClasses) {
						SootMethod invokedMethod = invokeExpr.getMethod();
						SootMethod m = sc.getMethod(invokedMethod.getSubSignature());
						addEdge(currentMethod, m, cg);
					}
				}
            }
        }
    }
    
    private SootMethod getNextMethod(Unit unit, TypeAssignmentGraph typeAssignmentGraph, CallGraph initialCallGraph) {
    	Stmt stmt = (Stmt) unit;
        if((unit instanceof JAssignStmt && ((JAssignStmt) unit).containsInvokeExpr())) {
        	InvokeExpr invokeExpr = stmt.getInvokeExpr();
        	JAssignStmt assignStmt = (JAssignStmt) stmt;
            Value target = assignStmt.leftBox.getValue();
            	
            	typeAssignmentGraph.addNode(target);
            SootMethod m = invokeExpr.getMethod();
            if (m.isStatic()) {
            	PatchingChain<Unit> methodUnits = m.getActiveBody().getUnits();
            	for(Unit u: methodUnits) {
					if (u instanceof JReturnStmt) {
						Value op = ((JReturnStmt) u).getOp();
						RefType refType = ((RefType) op.getType());
						SootClass sootClass = refType.getSootClass();
				            	typeAssignmentGraph.addNode(op);
						 typeAssignmentGraph.tagNode(target, sootClass);
						typeAssignmentGraph.addEdge(target, op);
					}
            	}
			} else {
				Set<SootMethod> edges = initialCallGraph.edgesOutOf(invokeExpr.getMethod());
				for (SootMethod edge : edges) {

					SootClass decClass = edge.getDeclaringClass();
					typeAssignmentGraph.tagNode(target, decClass); 
				}
			}
			
        	SootMethod method = stmt.getInvokeExpr().getMethod();
         	return method;
        } else if(stmt.containsInvokeExpr()) {
        	Value value = stmt.getInvokeExprBox().getValue();
			if(value instanceof JSpecialInvokeExpr) {
				if(!typeAssignmentGraph.containsNode(value)) {
					if(!(value instanceof JSpecialInvokeExpr)) {
				            	typeAssignmentGraph.addNode(value);
					}
				}
				JSpecialInvokeExpr expre = (JSpecialInvokeExpr) value;
				SootMethodRef mr = expre.getMethodRef();
				Value v = ((JSpecialInvokeExpr) value).getBaseBox().getValue();
					typeAssignmentGraph.addNode(v);
				SootClass cl = mr.declaringClass();
				typeAssignmentGraph.tagNode(v, cl);
			}
        	SootMethod method = stmt.getInvokeExpr().getMethod();
        	return method;
        } else if (stmt.containsFieldRef()) {

			JAssignStmt assignStmt = (JAssignStmt) stmt;
			Value target = assignStmt.leftBox.getValue();

			Value value = assignStmt.rightBox.getValue();
			Set<SootClass> tags = typeAssignmentGraph.getNodeTags(value);
			
	            	typeAssignmentGraph.addNode(target);
	            	typeAssignmentGraph.addNode(value);
			typeAssignmentGraph.addEdge(target, value);
			for (SootClass sootClass : tags) {
				typeAssignmentGraph.tagNode(target, sootClass);
			}
		} else if (stmt instanceof JAssignStmt) {
			
			JAssignStmt assignStmt = (JAssignStmt) stmt;
            Value target = assignStmt.leftBox.getValue();
            SootClass sootClass = ((RefType)assignStmt.rightBox.getValue().getType()).getSootClass();
            	typeAssignmentGraph.addNode(target);
            Value v = assignStmt.rightBox.getValue();
            if (v instanceof JCastExpr) {
            	JCastExpr exp = (JCastExpr) v;
            	Value v2 = exp.getOp();
                 	typeAssignmentGraph.addNode(v2);
            	RefType type = (RefType)exp.getCastType();
            	typeAssignmentGraph.addEdge(target, v2);
            	typeAssignmentGraph.tagNode(target, type.getSootClass());
            } else if (v instanceof JNewExpr) {
            	JNewExpr ne = (JNewExpr) v;
            	Value v2 = assignStmt.rightBox.getValue();
            	typeAssignmentGraph.tagNode(target, sootClass);
            } 
			
		} 
        return null;
	}
    
    private void addEdge(SootMethod source, SootMethod target, CallGraph cg) {
		if(!cg.hasNode(source)) cg.addNode(source);
		if(!cg.hasNode(target)) cg.addNode(target);
		if(!cg.hasEdge(source, target)) cg.addEdge(source, target);
		
	}

	private void processInterfaceInvokeExpr(SootMethod currentMethod, InvokeExpr invokeExpr, TypeAssignmentGraph typeAssignmentGraph, CallGraph cg) {
    	SootClass sootClass;
    	Value target;
    	if(invokeExpr instanceof JVirtualInvokeExpr) {
    		sootClass = ((RefType) ((JVirtualInvokeExpr) invokeExpr).getBaseBox().getValue().getType()).getSootClass();
    		target = ((JVirtualInvokeExpr) invokeExpr).getBaseBox().getValue();
    	} else {
			sootClass = ((RefType) ((JInterfaceInvokeExpr) invokeExpr).getBaseBox().getValue().getType()).getSootClass();
			target = ((JInterfaceInvokeExpr) invokeExpr).getBaseBox().getValue();
			
    	}
    	Set<SootClass> nodetags = typeAssignmentGraph.getNodeTags(target);
		for(SootClass sc: nodetags) {
			SootMethod invokedMethod = invokeExpr.getMethod();
			SootMethod m = sc.getMethod(invokedMethod.getSubSignature());
			addEdge(currentMethod, m, cg);
		}
         	typeAssignmentGraph.addNode(target);
    	typeAssignmentGraph.tagNode(target, sootClass);
	}


	/**
     * You can use this class to represent your type assignment graph.
     * We do not use this data structure in tests, so you are free to use something else.
     * However, we use this data structure in our solution and it instantly supports collapsing strong-connected components.
     */
    private class TypeAssignmentGraph {
        private final Graph graph;
        private TarjanStronglyConnectedComponents tscc = new TarjanStronglyConnectedComponents();

        public TypeAssignmentGraph() {
            this.graph = new MultiGraph("tag");
        }

        private boolean containsNode(Value value) {
            return graph.getNode(createId(value)) != null;
        }

        private boolean containsEdge(Value source, Value target) {
            return graph.getEdge(createId(source) + "-" + createId(target)) != null;
        }

        private String createId(Value value) {
            if (value instanceof FieldRef) return value.toString();
            return Integer.toHexString(System.identityHashCode(value));
        }

        public void addNode(Value value) {
            if (!containsNode(value)) {
                Node node = graph.addNode(createId(value));
                node.setAttribute("value", value);
                node.setAttribute("ui.label", value);
                node.setAttribute("tags", new HashSet<SootClass>());
            }
        }

        public void tagNode(Value value, SootClass classTag) {
            if (containsNode(value))
                getNodeTags(value).add(classTag);
        }

        public Set<Pair<Value, Set<SootClass>>> getTaggedNodes() {
            return graph.getNodeSet().stream()
                    .map(n -> new Pair<Value, Set<SootClass>>(n.getAttribute("value"), (Set<SootClass>) n.getAttribute("tags")))
                    .filter(p -> p.second.size() > 0)
                    .collect(Collectors.toSet());
        }

        public Set<SootClass> getNodeTags(Value val) {
            return ((Set<SootClass>) graph.getNode(createId(val)).getAttribute("tags"));
        }

        public void addEdge(Value source, Value target) {
            if (!containsEdge(source, target)) {
                Node sourceNode = graph.getNode(createId(source));
                Node targetNode = graph.getNode(createId(target));
                if (sourceNode == null || targetNode == null)
                    log.error("Could not find one of the nodes. Source: " + sourceNode + " - Target: " + targetNode);
                graph.addEdge(createId(source) + "-" + createId(target),
                        sourceNode,
                        targetNode, true);
            }

        }

        public Set<Value> getTargetsFor(Value initialNode) {
            if (!containsNode(initialNode)) return Collections.emptySet();
            Node source = graph.getNode(createId(initialNode));
            Collection<Edge> edges = source.getLeavingEdgeSet();
            return edges.stream()
                    .map(e -> (Value) e.getTargetNode().getAttribute("value"))
                    .collect(Collectors.toSet());
        }

        /**
         * Use this method to start the SCC computation.
         */
        public void annotateScc() {
            tscc.init(graph);
            tscc.compute();
        }

        /**
         * Retrieve the index assigned by the SCC algorithm
         * @param value
         * @return
         */
        public Object getSccIndex(Value value) {
            if(!containsNode(value)) return null;
            return graph.getNode(createId(value)).getAttribute(tscc.getSCCIndexAttribute());
        }

        /**
         * Use this method to inspect your type assignment graph
         */
        public void draw() {
            graph.display();
        }
    }

    private class Pair<A, B> {
        final A first;
        final B second;

        public Pair(A first, B second) {
            this.first = first;
            this.second = second;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Pair<?, ?> pair = (Pair<?, ?>) o;

            if (first != null ? !first.equals(pair.first) : pair.first != null) return false;
            return second != null ? second.equals(pair.second) : pair.second == null;
        }

        @Override
        public int hashCode() {
            int result = first != null ? first.hashCode() : 0;
            result = 31 * result + (second != null ? second.hashCode() : 0);
            return result;
        }

        @Override
        public String toString() {
            return "(" + first +
                    ", " + second +
                    ')';
        }
    }

}
