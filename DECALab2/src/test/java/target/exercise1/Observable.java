package target.exercise1;

import java.util.Vector;

public class Observable {
    private boolean changed = false;
    private Vector<Observer> obs;

    /**
     * Construct an Observable with zero Observers.
     */

    public Observable() {
        obs = new Vector<>();
    }

    public synchronized void addObserver(Observer o) {
        if (o == null)
            throw new NullPointerException();
        if (!obs.contains(o)) {
            obs.addElement(o);
        }
    }

    protected synchronized void setChanged() {
        changed = true;
    }

    public void notifyObservers() {
        notifyObservers(null);
    }

    public void notifyObservers(Object arg) {
        Object[] arrLocal;

        synchronized (this) {
            if (!changed)
                return;
            arrLocal = obs.toArray();
            clearChanged();
        }

        for (int i = arrLocal.length-1; i>=0; i--)
            ((Observer)arrLocal[i]).update(this, arg);
    }

    protected synchronized void clearChanged() {
        changed = false;
    }
}
