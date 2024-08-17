package testcase;

import java.lang.reflect.Method;

public class Test4 {

	int test4_1() throws Exception { // 16 18 19 22
		// Define a local class with a method
		class LocalClass {
			public int add(Test4 a, Test4 b) {
				return 10;
			}
		}

		// Create an instance of the local class
		Object localInstance = new LocalClass();

		Test4 t1 = new Test4();
		Test4 t2 = new Test4();

		// Invoke the add method of the local class dynamically
		int result = (int) localInstance.getClass().getMethod("add", Test4.class, Test4.class)
				.invoke(localInstance, t1, t2);

		return result;
	}

	Test4 tt;

	int test4_2() throws Exception { // 39 43 46
		// Define a local class with a method
		class LocalClass {
			public int add(Test4 a, Test4 b) {
				return 10;
			}
		}

		// Create an instance of the local class
		Object localInstance = new LocalClass();

		Test4 t1 = new Test4();
		Test4 t2 = new Test4();
		t2.tt = new Test4();

		// Invoke the add method of the local class dynamically
		int result = (int) localInstance.getClass().getMethod("add", Test4.class, Test4.class)
				.invoke(localInstance, t1.tt, t2.tt);

		return result;
	}
}
