public class lab11 {
	public static void main(String[] args) {
		int n = Integer.parseInt(args[0]);
		assert (n > 0);                                                     // Assertion 1
		assert (n + (n-1)/9 == n + (n-1)/9) && (n > 0);                     // Assertion 2
		int b = n;
		assert (b + (n-1)/9 == n + (n-1)/9) && (n > 0);                     // Assertion 3
		int c = n;
		assert (b + (c-1)/9 == n + (n-1)/9) && (c > 0);                     // Assertion 4
		while (c >= 10) {
			assert  (b + (c-1)/9 == n + (n-1)/9)    && (c > 0) && (c >= 10); // Assertion 5
			assert ((b+1) + ((c-9)-1)/9 == n + (n-1)/9)        && (c-9 > 0); // Assertion 6
			c = c - 9;
			assert ((b+1) + (c-1)/9 == n + (n-1)/9) && (c > 0);              // Assertion 7
			b = b + 1;
			assert (b + (c-1)/9 == n + (n-1)/9)     && (c > 0);              // Assertion 8
		}
		assert (b + (c-1)/9 == n + (n-1)/9)        && (c > 0) && (c < 10);  // Assertion 9
		assert (b == n + (n-1)/9);                                          // Assertion 10
		System.out.printf("b = %d\n", b);
	}
}
