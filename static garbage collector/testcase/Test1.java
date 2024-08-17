class Test1Node {
	Test1Node f;
	Test1Node g;
	Test1Node() {}
}

public class Test1 {
	public static Test1Node global;
	public static void main(String[] args) {
		foo();
	}
	public static Test1Node foo(){
		Test1Node x = new Test1Node();
		Test1Node y = new Test1Node();
		y.f = new Test1Node();
		y = new Test1Node();
		bar(x, y);
		Test1Node z = y.f;
		Test1Node a = x.f;
		return x;
	}
	public static void bar(Test1Node p1, Test1Node p2){
		Test1Node v = new Test1Node();
		p1.f = v;	
	}
}