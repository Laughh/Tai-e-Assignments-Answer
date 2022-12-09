package pascal.taie.ir.stmt;

public class Test {
    public static void main(String[] args) {
        A a = new A();
        for(int i = 0; i < 10; ++i){
            System.out.println(A.arr[i]);
        }
        int[] temp = A.arr;
        int x = temp[2];
        x *= 2;
    }
}

class A{
    static int[] arr = new int[10];
}
