import java.util.List;
import java.util.ArrayList;

public class task6{

	public static void main(String[] args){
		List<String> L = new ArrayList<String>(){{add("abx");add("s32");add("2354");add("nnmd");}};
		System.out.println(L);
		System.out.println("Printing subsets...");
		System.out.println(genSubs(L));


	}



	public static List<String> genSubs(List<String> L){
		int size = L.size();
		String temp = "";
		List<String> returnList = new ArrayList<String>();
	
		//loop runs until 2^n
		for(int i = 0; i < (1<<size); i++){
			temp = "{";
			
			for(int j = 0; j < size; j++){
				if((i & (1<<j)) > 0) {
					temp+=L.get(j);
					temp+= ",";
				}
			}
		
			temp+= "}";
		
			returnList.add(temp);
		}
	
		return returnList;
	}



}
