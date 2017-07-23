/*
 ID:l_coder1
 LANG:JAVA
 TASK:combo
 */
//package stage1_3;
import java.io.*;
import java.util.*;
import java.math.*;
public class combo {

	public static void main(String[] args) throws IOException {
		// TODO Auto-generated method stub
		BufferedReader f=new BufferedReader(new FileReader("combo.in"));
		PrintWriter out=new PrintWriter(new BufferedWriter(new FileWriter("combo.out")));
		StringTokenizer sn=new StringTokenizer(f.readLine());
		int N=Integer.parseInt(sn.nextToken());
		int []a=new int[3];
		int []b=new int[3];
		StringTokenizer sa=new StringTokenizer(f.readLine());
		for(int i=0;i<3;i++){
			a[i]=Integer.parseInt(sa.nextToken());
		}
		StringTokenizer sb=new StringTokenizer(f.readLine());
		for(int i=0;i<3;i++){
			b[i]=Integer.parseInt(sb.nextToken());
		}
		
		int []c=new int[3];
		
		if(N<=5){
			out.println(Integer.toString((N*N*N)));
		}else{
			for(int i=0;i<3;i++){
				int dl=Math.abs(a[i]-b[i]);
				int dr=N-dl;
				if(dl<=4){
					c[i]+=5-dl;
				}else{
					
				}
				if(dr<=4){
					c[i]+=5-dr;
				}else{
					
				}
			}
			out.println(250-c[0]*c[1]*c[2]);
		}
		out.close();
	}

}
