package analysis;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

import heros.DefaultSeeds;
import heros.EdgeFunction;
import heros.EdgeFunctions;
import heros.FlowFunction;
import heros.FlowFunctions;
import heros.InterproceduralCFG;
import heros.JoinLattice;
import heros.edgefunc.EdgeIdentity;
import heros.flowfunc.Identity;
import soot.Local;
import soot.NullType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.ide.DefaultJimpleIDETabulationProblem;

public class IDELinearConstantAnalysisProblem extends DefaultJimpleIDETabulationProblem<Local, Integer, InterproceduralCFG<Unit, SootMethod>> {

    protected InterproceduralCFG<Unit, SootMethod> icfg;

    public IDELinearConstantAnalysisProblem(InterproceduralCFG<Unit, SootMethod> icfg) {
        super(icfg);
        this.icfg = icfg;
    }

    @Override
    protected EdgeFunction<Integer> createAllTopFunction() {
        // TODO: Implement this function to return a special EdgeFunction that
        // represents 'no information' at all, that is used to initialize the
        // data-flow fact's values.
        return null;
    }

    // TODO: Implement this JoinLattice factory function, to return the lattice
    // for your data-flow analysis. The JoinLattice implementation states what
    // the top and bottom element are in your analysis's underlying lattice.
    // Additionally it states how to join two values in the lattice.
    // It probably makes sense to have an additional global variable in this
    // description class that represents the BOTTOM element; that will surely
    // become handy for the implementation of the EdgeFunctions.
    @Override
    protected JoinLattice<Integer> createJoinLattice() {
        return new JoinLattice<Integer>() {
            @Override
            public Integer topElement() {
                return null;
            }

            @Override
            public Integer bottomElement() {
                return null;
            }

            @Override
            public Integer join(Integer left, Integer right) {
                return null;
            }
        };
    }

    // TODO: You have to implement the FlowFunctions interface.
    // This is very similar to the IFDS analysis, but this time your just use
    // Local as type of the data-flow facts. Do not worry about a Local's value
    // here (the EdgeFunctions will take care of this job), just generate and
    // kill constant Locals when adequate.
    @Override
    protected FlowFunctions<Unit, Local, SootMethod> createFlowFunctionsFactory() {
        return new FlowFunctions<Unit, Local, SootMethod>() {
            @Override
            public FlowFunction<Local> getNormalFlowFunction(Unit curr, Unit succ) {
                // TODO: Implement this flow function factory to obtain an intra-procedural data-flow analysis.
                return Identity.v();
            }

            @Override
            public FlowFunction<Local> getCallFlowFunction(Unit callStmt, SootMethod dest) {
                // TODO: Implement this flow function factory to map the actual into the formal arguments.
                // Caution, actual parameters may be integer literals as well.
                return Identity.v();
            }

            @Override
            public FlowFunction<Local> getReturnFlowFunction(Unit callSite, SootMethod calleeMethod, Unit exitStmt, Unit returnSite) {
                // TODO: Map the return value back into the caller's context if applicable.
                // Since Java has pass-by-value semantics for primitive data types, you do not have to map the formals
                // back to the actuals at the exit of the callee.
                return Identity.v();
            }

            @Override
            public FlowFunction<Local> getCallToReturnFlowFunction(Unit callSite, Unit returnSite) {
                // TODO: getCallToReturnFlowFunction can be left to return id in many analysis; this time as well?
                return Identity.v();
            }
        };
    }

    // TODO: You have to implement the EdgeFunctions interface.
    // The EdgeFunctions take care of the actual value computation within this
    // linear constant propagation. An EdgeFunction is basically the
    // non-evaluated function representation of a constant Integer value
    // (or better its computation).
    // Similar to the FlowFunctions you may return different EdgeFunctions
    // depending on the current statement you are looking at.
    // An EdgeFunction describes an IDE lambda function on an exploded
    // super-graph edge from 'srcNode' to 'tgtNode', for instance, when looking
    // at 'getNormalEdgeFunction'. Do you have to implement all EdgeFunction
    // factory methods for the linear constant propagation?
    // Before you start, let us clarify the EdgeFunction interface:
    //        public interface EdgeFunction<V> {
    //          // This is where the magic happens and the most important
    //          // function of this interface. In compute targets your encode
    //          // the actual lambda function that describes what operation is
    //          // performed on an incoming Integer. This function can for
    //          // instance return a number, pass it as identity or perform
    //          // furth arithmetic operations on it.
    //          V computeTarget(V source);
    //          // In composeWith you are able to describe how two EdgeFunctions
    //          // can be composed with each other. You probably would like to
    //          // create a new class implementeing the EdgeFunction interface
    //          // and is able compose two EdgeFunctions.
    //          EdgeFunction<V> composeWith(EdgeFunction<V> secondFunction);
    //          // As the name suggests this function states how two
    //          // EdgeFunctions have to be joined. Remember that EdgeFunctions
    //          // are non-evaluated constant values.
    //          EdgeFunction<V> joinWith(EdgeFunction<V> otherFunction);
    //          // This function tells if 'this' EdgeFunction and the 'other'
    //          // EdgeFunction are equal.
    //          public boolean equalTo(EdgeFunction<V> other);
    //        }
    // Happy data-flow analysis ;-)
    @Override
    protected EdgeFunctions<Unit, Local, SootMethod, Integer> createEdgeFunctionsFactory() {
        return new EdgeFunctions<Unit, Local, SootMethod, Integer>() {
            @Override
            public EdgeFunction<Integer> getNormalEdgeFunction(Unit src, Local srcNode, Unit tgt, Local tgtNode) {
                return EdgeIdentity.v();
            }

            @Override
            public EdgeFunction<Integer> getCallEdgeFunction(Unit callStmt, Local srcNode, SootMethod destinationMethod, Local destNode) {
                return EdgeIdentity.v();
            }

            @Override
            public EdgeFunction<Integer> getReturnEdgeFunction(Unit callSite, SootMethod calleeMethod, Unit exitStmt, Local exitNode, Unit returnSite, Local retNode) {
                return EdgeIdentity.v();
            }

            @Override
            public EdgeFunction<Integer> getCallToReturnEdgeFunction(Unit callStmt, Local callNode, Unit returnSite, Local returnSideNode) {
                return EdgeIdentity.v();
            }
        };
    }

    @Override
    protected JimpleLocal createZeroValue() {
        return new JimpleLocal("<<zero>>", NullType.v());
    }

    @Override
    public Map<Unit, Set<Local>> initialSeeds() {
        for (SootClass c : Scene.v().getApplicationClasses()) {
            for (SootMethod m : c.getMethods()) {
                if (!m.hasActiveBody()) {
                    continue;
                }
                if (m.getName().equals("entryPoint")) {
                    return DefaultSeeds.make(Collections.singleton(m.getActiveBody().getUnits().getFirst()), zeroValue());
                }
            }
        }
        throw new IllegalStateException("scene does not contain 'entryPoint'");
    }

}
