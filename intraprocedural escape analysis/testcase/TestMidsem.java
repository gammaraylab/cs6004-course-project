package testcase;

public class TestMidsem {
	class NodeMidesem{
		NodeMidesem f;
		NodeMidesem g;
	}
    public static void main(String[] args){
	}
	public NodeMidesem foo(){ // 11
		NodeMidesem x= new NodeMidesem();
		NodeMidesem p =x;
		return p;
	}
	class NodeMidesemA{ NodeMidesemB g;}
	class NodeMidesemB{ int x;}
	class NodeMidesemD{
		NodeMidesemA f;
		public void foo(NodeMidesemD q){ // 23, 25
			NodeMidesemD a = new NodeMidesemD();
			NodeMidesemA b = new NodeMidesemA();
			a.f = new NodeMidesemA();
			NodeMidesemA p = a.f;
			a.f.g= new NodeMidesemB();
			NodeMidesemB x= bar (p,q);
		}
		public NodeMidesemB bar(NodeMidesemA p, NodeMidesemD q){ // 29, 30
			q.f = new NodeMidesemA();
			NodeMidesemB y= new NodeMidesemB();
			return y;
		}
	}
}