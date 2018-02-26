

public class Task5 {

	public static void main(String[] args) {
		// TODO Auto-generated method stub
		System.out.println(gcd(84,18));	//output should be 6
		System.out.println(gcd(3888, 524)); //output should be 4
		System.out.println(gcd(71,15)); //share no common factors output should be 1

	}
	
	
	static int gcd(int a, int b){
			int temp;
			while(b > 0){
				
				temp = b; 
				b = a%b;
				a = temp;
				
			}
		return a;
	}

}
