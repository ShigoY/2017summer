package stage1_2;
/*
ID: lcoder1
LANG: JAVA
TASK: beads
 */
import java.io.*;
import java.util.*;

public class beads {

	public static void main(String[] args) throws IOException{
		// TODO Auto-generated method stub
		BufferedReader f=new BufferedReader(new FileReader("beads.in"));
		PrintWriter out=new PrintWriter(new BufferedWriter(new FileWriter("beads.out")));
		
		StringTokenizer st1=new StringTokenizer(f.readLine());
		int N=Integer.parseInt(st1.nextToken());
		StringBuffer beans=new StringBuffer(f.readLine());
		
		int maxLength=0;
		char pre=beans.charAt(0);
		char curr=' ';
		int left=1;
		int right=1;
		int solo=0;
		for(int i=1;i<N;i++){
			curr=beans.charAt(i);
			
			if(curr!=pre){
				//start the left right search
				int index_l=(i-2+N)%N;
				int index_r=(i+1)%N;
				char pre_l=pre;
				char pre_r=curr;
				char curr_l=beans.charAt(index_l);
				char curr_r=beans.charAt(index_r);
				
				while(curr_l==pre_l||curr_l=='w'||pre_l=='w'){
					if(curr_l=='w'&&pre_l!='w'){
						index_l--;
						left++;
					}else if(pre_l=='w'&&curr_l!='w'){
						pre_l=curr_l;
						index_l--;
						left++;
					}else{
						index_l--;
						left++;
					}
					
					curr_l=beans.charAt((index_l+N)%N);
				}
				
				while(curr_r==pre_r||curr_r=='w'||pre_r=='w'){
					if(curr_r=='w'&&pre_r!='w'){
						index_r++;
						right++;
					}else if(pre_r=='w'&&curr_r!='w'){
						pre_r=curr_r;
						index_r++;
						right++;
					}else{
						index_r++;
						right++;
					}
					curr_r=beans.charAt(index_r%N);
				}
				
				if(maxLength<left+right){
						maxLength=left+right;
				}
				left=1;
				right=1;
				
			}else{
				solo++;
			}
			
			pre=curr;		
		}
		if(solo==N-1){
			maxLength=N;
		}
		
		out.println(maxLength);
		out.close();
	}
}
