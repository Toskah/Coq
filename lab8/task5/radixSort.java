
import java.util.*;
import java.io.*;

public class radixSort {
   static int[] a;
   static int   n;
   static char  c;

   static public void printData(int k) {
      System.out.format("\n\n");
      if (k>0) System.out.format("Sort on Digit %d\n", k);
      for (int i=0; i<n; i++) System.out.format("%9d\n",a[i]); 
   }
	/*
   static public void radixSort(int[] a, int k) {
      if (k==0) return;
      radixSort(a,k-1);
      sortByDigit.stableSort(a,k);
      if (c=='Y') printData(k);
   }*/
   
   static public void radixSort(int[] a){
	   
		for(int k = 1; k <=9; k++){  
		   sortByDigit.stableSort(a, k);
		   if(c == 'Y') printData(k);
		}   
	   
   }

   public static void main(String[] args) throws IOException {
      System.out.print("Enter the number of data to generate/sort: ");
      n = (new Scanner(System.in)).nextInt();
      a = new int[n];

      System.out.print("Do you want to print the data and intermediate results? (Y/N) ");
      c = (char) System.in.read();
	  
	  long startTime = System.nanoTime();
      Random r = new Random();
      for (int i=0; i<n; i++) a[i] = r.nextInt(1000000000);
	  long endTime = System.nanoTime();
	  System.out.println("Runtime for num gen was: " + ((endTime - startTime) / 1000000 )+ "");
      if (c=='Y') printData(0);
	 
	  startTime = System.nanoTime();	
      radixSort(a); // sort by all 9 digits
	  endTime = System.nanoTime();
	  System.out.println("Runtime for sorting was: " + ((endTime - startTime) / 1000000 )+ ""); 
	 
	  startTime = System.nanoTime();		
      for (int i=0; i<n-1; i++) // check to see if data is sorted
          if (a[i]>a[i+1]) {
             System.out.println("mistake at " + i);
             return;
      }
	  endTime = System.nanoTime();
	  System.out.println("Runtime for correctness check was: " + ((endTime - startTime) / 1000000 )+ ""); 
   }
}