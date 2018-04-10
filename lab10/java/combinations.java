import java.util.List;
import java.util.ArrayList;

public class combinations{

	public static void main(String[] args){
		List<String> L = new ArrayList<String>(){{add("abx");add("s32");add("2354");add("nnmd");}};
		System.out.println(comb(L,0));
		System.out.println(comb(L,1));
		System.out.println(comb(L,2));
		System.out.println(comb(L,3));
		System.out.println(comb(L,4));
	}

	public static List<List<String>> comb(List<String> L , int k){
		if(k == 0) return new ArrayList<List<String>>(){{add(new ArrayList<String>());}};
		if(L.size() == k) return new ArrayList<List<String>>(){{add(new ArrayList<String>(L));}};

		List<List<String>> L1 = comb(L.subList(1,L.size()),k);
		List<List<String>> L2 = comb(L.subList(1,L.size()),k-1);

		for(List<String> list : L2) list.add(L.get(0));
		L1.addAll(L2);
		
		return L1;
	}

}
