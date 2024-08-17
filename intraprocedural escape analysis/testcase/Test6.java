package testcase;

public class Test6 {
	int a;
	float b;

	public void test6_1(Test6 a) {
		Test6 t1 = new Test6();
		Test6[] t2 = new Test6[10];

		t2[5].a = t1.a;
	}

	public Test6 test6_2(boolean b) throws Exception { // 16 21 29
		Test6 t1 = new Test6();
		Test6 t2 = new Test6();
		Test6 t3 = new Test6();
		Test6[] t4 = new Test6[10];

		if (!b) {
			t4[4] = new Test6();
		}
		
		t4[1].a = 5 + 1;
		t4[1].a = t4[1].a + t4[5].a;

		if (b) {
			t3 = t2;
			throw new Exception(t3.toString());
		} else {
			t3 = t1;
			t3 = t4[5];
		}
		return t3;
	}

	public void test6_3(boolean b) { // 38 39
		Test6 o6 = new Test6();
		Test6E o6e = new Test6E();
		if (b) {
			test6_1(o6e);
		} else {
			o6.test6_1(o6);
		}
		o6 = (Test6) o6e;
	}

	public Test6 test6_4(boolean b) { // 51
		Test6[] t4 = new Test6[10];
		Test6 a = t4[4];
		t4[4] = new Test6();
		if (b) {
			return t4[10];
		}
		return a;
	}

	public Test6 test6_5() { // Nothing allocated on this stack escapes, as per Java semantics
		Test6[] t4 = new Test6[10];
		Test6 a = t4[4];
		t4[4] = new Test6();
		return a;
	}

}

class Test6E extends Test6 {

}