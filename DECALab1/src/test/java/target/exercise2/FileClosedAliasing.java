package target.exercise2;

public class FileClosedAliasing {
	private static File staticFile;
	
	public void test1() {
		File file = new File();
		File alias = file;
		file.open();
		alias.close();
	}
	
	public void test2()
	{
		staticFile=new File();
		File file=staticFile;
		staticFile.open();
		file.close();
	}
}
