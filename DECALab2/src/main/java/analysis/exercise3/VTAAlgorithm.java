package analysis.exercise3;

import analysis.CallGraph;
import analysis.CallGraphAlgorithm;
import analysis.exercise1.CHAAlgorithm;
import soot.Scene;

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

    }

}
