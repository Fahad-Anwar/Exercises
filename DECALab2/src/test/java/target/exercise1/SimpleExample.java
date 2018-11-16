package target.exercise1;


public class SimpleExample implements Observer {
    public static void main(String[] args) {
        SimpleExample m = new SimpleExample();
        Subject s = new Subject();
        s.addObserver(m);
        s.modify();
    }

    public void update(Observable o, Object arg) {
        System.out.println(o+" notified me!");
    }

    static class Subject extends Observable  {
        public void modify() {
            setChanged();
            notifyObservers();
        }
    }
}
