/*
ID: lcoder1
LANG: JAVA
TASK: palsquare
 */
//package stage1_2;

import java.io.*;
import java.util.*;

class palsquare {
	public static char a[]={'0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F','G','H','I','J'};
	public static boolean isParlindrome(String snum,int start,int end){
		if(start>=end){
			return true;
		}else{
			if(snum.charAt(start)==snum.charAt(end)){
				start++;
				end--;
				if(isParlindrome(snum,start,end)){
					return true;
				}
			}
		}
		return false;
	}
	
	public static String get_baseX(int num,int base){
		StringBuffer s=new StringBuffer();
		int r;
		do{
			r=num%base;
			num=num/base;
			
			s.append(a[r]);
		}while(num!=0);
		
		return s.reverse().toString();
	}
	
	public static void main(String[] args) throws IOException {
		// TODO Auto-generated method stub
		BufferedReader f=new BufferedReader(new FileReader("palsquare.in"));
		PrintWriter out=new PrintWriter(new BufferedWriter(new FileWriter("palsquare.out")));
		StringTokenizer st=new StringTokenizer(f.readLine());
		int base=Integer.parseInt(st.nextToken());

		for(int i=1;i<=300;i++){

			String base_left=get_baseX(i,base);
			String base_right=get_baseX(i*i,base);
			if(isParlindrome(base_right,0,base_right.length()-1)){
				out.println(base_left+" "+base_right);
			}
		}
		out.close();
		
	}

}
