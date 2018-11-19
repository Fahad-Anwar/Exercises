package target.exercise2;

public class FileNotClosed {
	
	public void test1() {
		File file = new File();
		file.open();
	}

	public void test2() {
		File file = new File();
		file.open();
		file = new File();
		file.close();
	}

	public void test3() {
		File file = new File();
		file.open();
		file.close();
		file.open();
	}
	
}
