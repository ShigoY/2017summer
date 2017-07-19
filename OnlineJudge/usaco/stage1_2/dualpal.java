/*
ID: lcoder1
LANG: JAVA
TASK: dualpal
 */
//package stage1_2;

import java.util.*;
import java.io.*;

class dualpal {
	
	static char []a={'0','1','2','3','4','5','6','7','8','9'};
	
	public static boolean isPalindrome(String str){
		int n=str.length();
		for(int i=0;i<=n/2;i++){
			if(str.charAt(i)!=str.charAt(n-i-1)){
				return false;
			}
		}
		return true;
	}
	
	public static String get_baseX(int num,int base){
		String s="";
		int res;
		do{
			res=num%base;
			num=num/base;
			s+=a[res];
		}while(num!=0);
		
		return s;
	}
	
//	public static boolean isDualPalindrome(int num){
//		int count=0;
//		for(int i=2;i<=10;i++){
//			String result=get_baseX(num,i);
//			if(isPalindrome(result)){
//				if(count<2){
//					count++;
//				}else{
//					return true;
//				}
//			}
//		}
//		return false;
//	}
	
	public static void main(String[] args) throws IOException{
		// TODO Auto-generated method stub
		BufferedReader f=new BufferedReader(new FileReader("dualpal.in"));
		PrintWriter out=new PrintWriter(new BufferedWriter(new FileWriter("dualpal.out")));
		StringTokenizer st=new StringTokenizer(f.readLine());
		int N=Integer.parseInt(st.nextToken());
		int S=Integer.parseInt(st.nextToken());
		
		int count=0;
		int i=S+1;
		while(count<N){
			int c=0;
			for(int k=2;k<=10;k++){
				String result=get_baseX(i,k);
				if(isPalindrome(result)){
					if(c<1){
						c++;
					}else{
						out.println(i);
						count++;
						break;
					}
				}
			}
			i++;
		}
		out.close();
	}

}
