import java.util.List;
import java.util.ArrayList;

public class ListTest {

	public static void main(String[] args){
		System.out.println(subsets(new ArrayList<String>()));
		List<String> L = new ArrayList<String>(){{add("abx");add("s32");add("2354");add("nnmd");}};
		System.out.println(L);
		System.out.println(subsets(L));


	}
	
	//enumerate all subsets of the set of objects given in list L
	public static List<List<String>> subsets(List<String> L) {
		if (L.isEmpty()) return new ArrayList<List<String>>(){{add(new ArrayList<String>());}};
		
		List<List<String>> L1 = subsets(L.subList(1,L.size()));
		//System.out.println("Printing L1: " + L1);
		List<List<String>> L2 = subsets(L.subList(1,L.size()));
		
		for (List<String> list : L2) list.add(L.get(0));
		//System.out.println("Printing L2: " + L2);
		L1.addAll(L2);
		
	return L1;
	}
}
