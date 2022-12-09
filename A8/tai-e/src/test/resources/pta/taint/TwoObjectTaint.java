interface Iterator {
    String next();
    void f(String s);
}

class TwoObjectTaint {
    public static void main(String[] args) {
        List l1 = new List();
        l1.add(SourceSink.source());
        List l2 = new List();
        l2.add(SourceSink.source());

        Iterator i1 = l1.iterator();
        SourceSink.sink(i1.next());
        Iterator i2 = l2.iterator();
        SourceSink.sink(i2.next());

        String taint = SourceSink.source();
        i1.f(taint);
    }
}

class List {

    String element;

    void add(String e) {
        this.element = e;
    }

    Iterator iterator() {
        return new ListIterator();
    }

    class ListIterator implements Iterator {
        public String next() {
            return element;
        }

        public void f(String s){
//            System.out.println(s);
        }
    }
}