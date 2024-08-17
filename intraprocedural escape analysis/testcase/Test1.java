
class Test1Node {
	Test1Node f;
	Test1Node g;
}
public class Test1 {
	public static Test1Node global;
	public static void main(String[] args) {
		foo();
	}
	public static Test1Node foo(){ // 14 15 16 17
		Test1Node x = new Test1Node();
		x.f = new Test1Node();
		x.f.g = new Test1Node(); 
		Test1Node y = new Test1Node(); 
		Test1Node z = new Test1Node();
		y.f = z;
		bar(x.f, y);
		return y.f;
	}
	public static void bar(Test1Node p1, Test1Node p2){ // 24
		Test1Node w = new Test1Node();
		w.f = new Test1Node(); 
		p2.f = w.f;		
	}
}
