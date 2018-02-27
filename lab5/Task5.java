

public class Task5 {

	public static void main(String[] args) {
		// TODO Auto-generated method stub
		System.out.println(gcd(84,18));	//output should be 6
		System.out.println(gcd(3888, 524)); //output should be 4
		System.out.println(gcd(75,15)); //share no common factors output should be 1

	}
	
	
	static int gcd(int a, int b){
			int temp;
			while(b > 0){
				
				temp = b;
				System.out.println("Temp" + temp);
				b = a%b;
				System.out.println( " b " + b);
				a = temp;
				
				
			}
		return a;
	}
	

}
