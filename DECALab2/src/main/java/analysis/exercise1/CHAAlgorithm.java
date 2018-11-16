package analysis.exercise1;

import analysis.CallGraph;
import analysis.CallGraphAlgorithm;
import soot.Scene;


public class CHAAlgorithm extends CallGraphAlgorithm {

    @Override
    protected String getAlgorithm() {
        return "CHA";
    }

    @Override
    protected void populateCallGraph(Scene scene, CallGraph cg) {
        // Your implementation goes here, also feel free to add methods as needed
        // To get your entry points we prepared getEntryPoints(scene) in the superclass for you


    }

}
