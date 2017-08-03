/*
 ID:l_coder1
 LANG:JAVA
 TASK:pprime 
 */
//package stage1_5;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.StringTokenizer;

public class pprime {
	private static int a;
	private static int b;
	private static PrintWriter out;
	
	public static boolean isPrime(int n){
		int i=2;
		while(i*i<=n){
			if(n%i==0){
				return false;
			}
			i++;
		}
		return true;
	}
	
	//in this case we can assign number 9 as the default value
	public static int getDigit(int n){
		if(n>=5&&n<=9){
			return 1;
		}else if(n>=10&&n<=99){
			return 2;
		}else if(n>=100&&n<=999){
			return 3;
		}else if(n>=1000&&n<=9999){
			return 4;
		}else if(n>=10000&&n<=99999){
			return 5;
		}else if(n>=100000&&n<=999999){
			return 6;
		}else if(n>=1000000&&n<=9999999){
			return 7;
		}else if(n>=10000000&&n<=99999999){
			return 8;
		}else{
			return 9;
		}
	}
	
	public static void t1(){
		if(5>=a&&5<=b){
			out.println(5);
		}
		if(7>=a&&7<=b){
			out.println("7");
		}
	}
	
	public static void t2(){
		if(11>=a&&11<=b){
			out.println("11");
		}
	} 
	
	public static void t3(){
		for(int d1=1;d1<=9;d1++)
			for(int d2=0;d2<=9;d2++){
				int num=101*d1+10*d2;
				if(num>=a&&num<=b&&isPrime(num)){
					out.println(Integer.toString(num));
				}
			}
				
	}
	
	public static void t5(){
		for(int d1=1;d1<=9;d1++)
			for(int d2=0;d2<=9;d2++)
				for(int d3=0;d3<=9;d3++){
					int num=10001*d1+1010*d2+100*d3;
					if(num>=a&&num<=b&&isPrime(num)){
						out.println(Integer.toString(num));
					}
				}
	}
	
	public static void t7(){
		for(int d1=1;d1<=9;d1++)
			for(int d2=0;d2<=9;d2++)
				for(int d3=0;d3<=9;d3++)
					for(int d4=0;d4<=9;d4++){
						int num=1000001*d1+100010*d2+10100*d3+1000*d4;
						if(num>=a&&num<=b&&isPrime(num)){
							out.println(Integer.toString(num));
						}
					}
	}
	
	public static void main(String[] args) throws IOException{
		// TODO Auto-generated method stub
		BufferedReader f=new BufferedReader(new FileReader("pprime.in"));
		out=new PrintWriter(new BufferedWriter(new FileWriter("pprime.out")));
		StringTokenizer s=new StringTokenizer(f.readLine());
		a=Integer.parseInt(s.nextToken());
		b=Integer.parseInt(s.nextToken());
		int ca=getDigit(a);
		int cb=getDigit(b);
		for(int i=ca;i<=cb;i++){
			switch(i){
			case 1:t1();break;
			case 2:t2();break;
			case 3:t3();break;
			case 5:t5();break;
			case 7:t7();break;
			default:break;
			}
		}
		out.close();
	}

}
