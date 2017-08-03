/*
ID: l_coder1
LANG: JAVA
TASK:skidesign
*/
//package stage1_3;
import java.io.*;
import java.util.*;

public class skidesign {

	final static int MAX=1000000;
	public static void main(String[] args) throws IOException{
		// TODO Auto-generated method stub
		BufferedReader f=new BufferedReader(new FileReader("skidesign.in"));
		PrintWriter out=new PrintWriter(new BufferedWriter(new FileWriter("skidesign.out")));
		StringTokenizer stn=new StringTokenizer(f.readLine());
		int n=Integer.parseInt(stn.nextToken());
		int []h=new int[1000];
		for(int i=0;i<n;i++){
			StringTokenizer s=new StringTokenizer(f.readLine());
			h[i]=Integer.parseInt(s.nextToken());
		}
		
		int min=MAX;
		
		for(int i=0;i<=83;i++){
			int tmp=0;
			for(int j=0;j<n;j++){
				if(h[j]<i){
					tmp+=(i-h[j])*(i-h[j]);
				}
				if(h[j]>i+17){
					tmp+=(h[j]-i-17)*(h[j]-i-17);
				}
			}
			if(tmp<min){
				min=tmp;
			}
		}
		
		out.println(Integer.toString(min));
		out.close();
	}

}
