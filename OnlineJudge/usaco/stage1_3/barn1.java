/*
ID: l_coder1
LANG: JAVA
TASK: barn1
 */

//package stage1_3;
import java.io.*;
import java.util.*;

class barn1 {
	public static void main(String[] args) throws IOException{
		// TODO Auto-generated method stub
		BufferedReader f=new BufferedReader(new FileReader("barn1.in"));
		PrintWriter out=new PrintWriter(new BufferedWriter(new FileWriter("barn1.out")));
		StringTokenizer s=new StringTokenizer(f.readLine());
		int M=Integer.parseInt(s.nextToken());
		int S=Integer.parseInt(s.nextToken());
		int C=Integer.parseInt(s.nextToken());
		List<Integer> occ=new ArrayList<Integer> ();
		for(int i=0;i<C;i++){
			StringTokenizer sc=new StringTokenizer(f.readLine());
			occ.add(Integer.parseInt(sc.nextToken()));
		}
		
		Collections.sort(occ);
		
		List<Integer> blank=new ArrayList<Integer>();
		int count=1;
		int length=1;
		for(int i=1;i<C;i++){
			int gap=occ.get(i)-occ.get(i-1);
			if(gap!=1){
				blank.add(gap-1);
				count++;
			}else{
				
			}
			length++;
		}
		
		Collections.sort(blank);
		
		for(int i=0;i<blank.size();i++){
			if(count<=M){
				
				break;
			}else{
				length+=blank.get(i);
				count--;
			}
		}
		out.println(Integer.toString(length));
		//bitte nicht vergessen
		out.close();
	}

}
