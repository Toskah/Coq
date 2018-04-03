public class task6{	
	
	public static void main (String[] args){
		
		int count = 0;
		
		for(int i = 0;  i < 65536; i++){
			
			String temp = Integer.toBinaryString(i);
			
			if(temp.contains("000")) {
				System.out.println(temp);
				count++;
			}
		}
		
		System.out.println(count);
	}
	
}