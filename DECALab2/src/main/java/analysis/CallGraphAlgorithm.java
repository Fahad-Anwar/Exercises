package analysis;

import soot.Scene;
import soot.SootMethod;

import java.util.stream.Stream;

public abstract class CallGraphAlgorithm {
    public CallGraph constructCallGraph(Scene scene) {
        CallGraph cg = new CallGraph(getAlgorithm());
        populateCallGraph(scene, cg);
        return cg;
    }

    protected Stream<SootMethod> getEntryPoints(Scene scene) {
        return scene.getApplicationClasses().stream().flatMap(c -> c.getMethods().stream()).filter(m -> m.getName().contains("main") && m.hasActiveBody());
    }

    protected abstract void populateCallGraph(Scene scene, CallGraph cg);

    protected abstract String getAlgorithm();
}
