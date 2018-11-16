package target.exercise2;

import soot.baf.SpecialInvokeInst;

public class Starter {
    public static void main(String[] args) {
        SomeInterface anObject = generateObject();

        anObject.doSomething();
    }

    private static SomeInterface generateObject() {
        String time = Long.toString(System.currentTimeMillis());
        char lastChar = time.charAt(time.length() - 1);

        switch (lastChar) {
            case 2 : return new LeafClass();
            case 3 : return new OtherLeafClass();
            case 4 : return new Specialization();
            default : return new Subclass();
        }



    }
}
