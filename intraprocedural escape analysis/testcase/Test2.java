package testcase;

public class Test2 {
	Test2 test2_1(Test2 p) { // 5
		Test2 t1 = new Test2();
		return t1;
	}

	Test2 test2_2(boolean b, boolean d) { // 10 11 12
		Test2 t1 = new Test2();
		Test2 t2 = new Test2();
		Test2 t3 = new Test2();

		while (b) {
			if (b && d) {
				return t1;
			} else {
				return t2;
			}
		}

		return t3;
	}

	Test2 test2_3(boolean b, boolean d) { // 27
		Test2 t1 = new Test2();
		Test2 t2 = new Test2();

		while (b) {
			if (b && d) {
				Test2 temp;
				temp = t1;
				t1 = t2;
				test2_1(t1);
				t1 = temp;
				return null;
			} else {
				t1 = t2;
				return t1;
			}
		}

		return null;
	}

	Test2 test2_4(boolean b, boolean d) { // 47 48
		Test2 t1 = new Test2();
		Test2 t2 = new Test2();

		while (b) {
			if (b && d) {
				test2_1(t1);
			} else {
				test2_1(t2);
			}
		}

		return null;
	}

	Test2 f, g;

	Test2 test2_5(Test2 x, boolean b) { // 69
		while (b) {
			x = x.f;
		}

		if (b) {
			return new Test2();
		}
		return x;
	}

	Test2 test2_6() { // 75 78
		Test2 x = new Test2(); // x -> O75
		Test2 y = x;           // x -> O75, y -> O75
		for (int i = 0; i < 10; i++) {
			y.f = new Test2();   // x -> O75, y -> O75 | O75.f -> O78
			y = y.f;             // x -> O75, y -> O78 | O75.f -> O78
		}
		return x;              // return O75 and O75.f
	}

	Test2 test2_8(Test2 global) { // 85 86
		global.f.g.g.f.f = new Test2();
		f = new Test2();
		return null;
	}

}
