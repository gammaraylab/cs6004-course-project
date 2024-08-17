package testcase;

public class Test3 {
	
	class MyException extends Exception {
		Test3 s;
	}

	Test3 f;
	void test3_1(Test3 p) { // 11
		Test3 t1 = new Test3();
		Test3 t2 = new Test3();
		p.f = t1;
		return;
	}

	void test3_2(Test3 p) { // 18
		Test3 a = new Test3();
		this.f = a;
		test3_1(this.f);
		return;
	}

	void test3_3(Test3 p, boolean b) throws MyException { // 25 26
		MyException m = new MyException();
		m.s = new Test3();
		if (b) {
			throw m;
		}
		return;
	}

	void test3_4(Test3 p, boolean b) throws MyException { // 34
		MyException m = new MyException();
		Test3 tt = new Test3();
		if (b) {
			throw m;
		} else {
			m.s = tt;
		}
		return;
	}

	// My answer is imprecise here, 47 does not really escape...
	Exception test3_5(Test3 p, boolean b) { // 46 47 56 58
		MyException m = new MyException();
		Test3 tt = new Test3();

		try {
			if (b) {
				throw m;
			} else {
				m.s = tt;
			}
		} catch (Exception e) { // The predecessors are both if and else branch (this is the cause of imprecision here)
			return new Exception();
		} 
		return new Exception();
	}

}
