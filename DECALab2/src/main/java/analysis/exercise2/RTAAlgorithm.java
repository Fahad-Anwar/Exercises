package analysis.exercise2;


import analysis.CallGraph;
import analysis.exercise1.CHAAlgorithm;
import soot.Scene;

public class RTAAlgorithm extends CHAAlgorithm  {

    @Override
    protected String getAlgorithm() {
        return "RTA";
    }

    @Override
    protected void populateCallGraph(Scene scene, CallGraph cg) {
        // Your implementation goes here, also feel free to add methods as needed
        // To get your entry points we prepared getEntryPoints(scene) in the superclass for you

    }

}
