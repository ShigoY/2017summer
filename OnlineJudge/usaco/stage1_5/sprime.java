/*
 ID:l_coder1
 LANG:JAVA
 TASK:sprime
 */
//package stage1_5;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.StringTokenizer;
public class sprime {

	private static PrintWriter out;
	private static int N;
	public static boolean isPrime(int N){
		int i=2;
		while(i*i<=N){
			if(N%i==0){
				return false;
			}
			i++;
		}
		return true;
	}
	
	public static void dfs(int num,int depth){
		if(depth==N){
			out.println(num);
			return;
		}
		for(int i=0;i<=9;i++){
			if(isPrime(num*10+i))
				dfs(num*10+i,depth+1);
		}
	}
	
	public static void main(String[] args) throws IOException {
		// TODO Auto-generated method stub
		BufferedReader f=new BufferedReader(new FileReader("sprime.in"));
		out=new PrintWriter(new BufferedWriter(new FileWriter("sprime.out")));
		N=Integer.parseInt((new StringTokenizer(f.readLine())).nextToken());
		dfs(2,1);
		dfs(3,1);
		dfs(5,1);
		dfs(7,1);
		out.close();
		
		
	}

}
