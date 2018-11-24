package target.exercise3;

import target.exercise2.*;

public class SimpleScenario {

    private static SomeInterface staticField;

    public static void main(String[] args) {

        SomeInterface leaf = new LeafClass();
        SomeInterface fourthLeaf = getFifthLeafClass();

        LeafClass aliasLeaf = (LeafClass)leaf;

        leaf.doSomething();
        fourthLeaf.doSomething();
        aliasLeaf.doSomething();

        staticField = new SixthLeafClass();

        SomeInterface newStuff = staticField;

        newStuff.doSomething();
    }

    private static SomeInterface getFifthLeafClass() {
        return new FifthLeafClass();
    }

}
