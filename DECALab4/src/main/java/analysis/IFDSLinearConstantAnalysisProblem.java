package analysis;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

import heros.DefaultSeeds;
import heros.FlowFunction;
import heros.FlowFunctions;
import heros.InterproceduralCFG;
import heros.flowfunc.Identity;
import heros.solver.Pair;
import soot.Local;
import soot.NullType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.ide.DefaultJimpleIFDSTabulationProblem;

public class IFDSLinearConstantAnalysisProblem extends DefaultJimpleIFDSTabulationProblem<Pair<Local, Integer>, InterproceduralCFG<Unit, SootMethod>> {

    protected final static int LOWER_BOUND = -1000;

    protected final static int UPPER_BOUND = 1000;

    protected InterproceduralCFG<Unit, SootMethod> icfg;

    public IFDSLinearConstantAnalysisProblem(InterproceduralCFG<Unit, SootMethod> icfg) {
        super(icfg);
        this.icfg = icfg;
    }

    @Override
    public Map<Unit, Set<Pair<Local, Integer>>> initialSeeds() {
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

    // TODO: You have to implement the FlowFunctions interface.
    // Use Pair<Local, Integer> as type for the data-flow facts.
    @Override
    protected FlowFunctions<Unit, Pair<Local, Integer>, SootMethod> createFlowFunctionsFactory() {
        return new FlowFunctions<Unit, Pair<Local, Integer>, SootMethod>() {
            @Override
            public FlowFunction<Pair<Local, Integer>> getNormalFlowFunction(Unit curr, Unit next) {
                // TODO: Implement this flow function factory to obtain an intra-procedural data-flow analysis.
                return Identity.v();
            }

            @Override
            public FlowFunction<Pair<Local, Integer>> getCallFlowFunction(Unit callsite, SootMethod dest) {
                // TODO: Implement this flow function factory to map the actual into the formal arguments.
                // Caution, actual parameters may be integer literals as well.
                return Identity.v();
            }

            @Override
            public FlowFunction<Pair<Local, Integer>> getReturnFlowFunction(Unit callsite, SootMethod callee, Unit exit, Unit retsite) {
                // TODO: Map the return value back into the caller's context if applicable.
                // Since Java has pass-by-value semantics for primitive data types, you do not have to map the formals
                // back to the actuals at the exit of the callee.
                return Identity.v();
            }

            @Override
            public FlowFunction<Pair<Local, Integer>> getCallToReturnFlowFunction(Unit callsite, Unit retsite) {
                // TODO: getCallToReturnFlowFunction can be left to return id in many analysis; this time as well?
                return Identity.v();
            }
        };
    }

    @Override
    protected Pair<Local, Integer> createZeroValue() {
        return new Pair<>(new JimpleLocal("<<zero>>", NullType.v()), Integer.MIN_VALUE);
    }

}
