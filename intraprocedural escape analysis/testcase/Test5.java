package testcase;
// Base interface with common methods
interface Test5Base {
	void test5_1();

	Test5 test5_2(boolean b);
}

// First interface extending Test5Base
interface Test5Interface1 extends Test5Base {
	void test5_3();
}

// Second interface extending Test5Base
interface Test5Interface2 extends Test5Base {
	void test5_3();
}

// Base class implementing Test5Base
class Test5BaseClass implements Test5Base {
	@Override
	public void test5_1() {
		System.out.println("Test5BaseClass: Implementing test5_1");
	}

	@Override
	public Test5 test5_2(boolean b) { // 30
		Test5 tt = new Test5();
		if (b) {
			tt = new Test5();
			return tt;
		} else {
			tt = null;
		}
		return tt;
	}
}

// Derived class implementing both interfaces
class Test5DerivedClass extends Test5BaseClass implements Test5Interface1, Test5Interface2 {
	@Override
	public void test5_3() {
		System.out.println("Test5DerivedClass: Implementing test5_3");
	}
}

public class Test5 {
	public void test5_4(String[] args) { // 49
		Test5DerivedClass derivedObj = new Test5DerivedClass();
		derivedObj.test5_1();
		derivedObj.test5_2(false);
		derivedObj.test5_3();
	}
}
