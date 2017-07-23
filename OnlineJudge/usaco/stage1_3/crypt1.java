/*
 ID: l_coder1
 LANG: JAVA
 TASK: crypt1
 */
//package stage1_3;
import java.io.*;
import java.util.*;
public class crypt1 {

	public static void main(String[] args) throws IOException{
		// TODO Auto-generated method stub
		BufferedReader f=new BufferedReader(new FileReader("crypt1.in"));
		PrintWriter out=new PrintWriter(new BufferedWriter(new FileWriter("crypt1.out")));
		StringTokenizer st=new StringTokenizer(f.readLine());
		int N=Integer.parseInt(st.nextToken());
		List<Integer> l_nums=new ArrayList<Integer>();
		StringTokenizer sn=new StringTokenizer(f.readLine());
		for(int i=0;i<N;i++){
			l_nums.add(Integer.parseInt(sn.nextToken()));
		}
		int sol=0;
		for(int i=100;i<=999;i++){
			for(int j=10;j<=99;j++){
				if(judge(i,l_nums)&&judge(j,l_nums)&&judge((j%10)*i,l_nums)&&judge((j/10)*i,l_nums)&&judge(i*j,l_nums)){
					if((j%10)*i>=100&&(j%10)*i<=999&&(j/10)*i>=100&&(j/10)*i<=999&&i*j>=1000&&i*j<=9999){
						sol++;
					}
				}
			}
		}
		out.println(Integer.toString(sol));
		//wichtig
		out.close();
	}
	
	public static boolean judge(int num,List<Integer> l){
		int res;
		while(num!=0){
			res=num%10;
			num=num/10;
			if(!l.contains(res)){
				return false;
			}
		}
		return true;
	}

}
