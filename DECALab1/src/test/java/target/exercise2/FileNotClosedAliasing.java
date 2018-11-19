package target.exercise2;

public class FileNotClosedAliasing {
	private static File staticFile;

	public void test1() {
		File file = new File();
		File alias = file;
		alias.open();
	}

	public void test2() {
		staticFile = new File();
		File file = staticFile;
		file.open();
	}

	public void test3() {
		File file = new File();
		staticFile = file;
		staticFile.open();
	}

	public void test4() {
		File file = new File();
		file.open();
		File alias1 = file;
		File alias2 = alias1;
		alias2.open();
		alias1.open();
	}
}
