package target.exercise2;

/**
 * 
 * This is the target class for TypeStateAnalysis.java
 *
 */
public class FileClosed {

	public void test1() {
		File file = new File();
		file.open();
		file.close();
	}

	public void test2() {
		File file = new File();
		file.open();
		if (file.size() > 1024) {
			file.close();
		} else {
			file.close();
		}
	}
}
