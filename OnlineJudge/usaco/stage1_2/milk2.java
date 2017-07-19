/*
ID: lcoder1
LANG: JAVA
TASK: milk2
 */



import java.util.*;
import java.io.*;
import java.util.List;

class milk2 {
	public static void main(String []args) throws IOException{
		BufferedReader f=new BufferedReader(new FileReader("milk2.in"));
		PrintWriter out=new PrintWriter(new BufferedWriter(new FileWriter("milk2.out")));
		StringTokenizer st1=new StringTokenizer(f.readLine());
		int N=Integer.parseInt(st1.nextToken());
		List<Integer> start=new ArrayList<Integer>();
		List<Integer> end=new ArrayList<Integer>();
		for(int i=0;i<N;i++){
			StringTokenizer sp=new StringTokenizer(f.readLine());
			start.add(Integer.parseInt(sp.nextToken()));
			end.add(Integer.parseInt(sp.nextToken()));
		}
		
		int min_start=start.get(0);
		int max_end=end.get(0);
		for(int i=1;i<N;i++){
			if(min_start>start.get(i)){
				min_start=start.get(i);
			}
			if(max_end<end.get(i)){
				max_end=end.get(i);
			}
		}
		
		int max_milked=0;
		int max_idle=0;
		int count=0;
		boolean flag=true;
		for(int i=min_start;i<=max_end;i++){
			boolean is_milked=isMilked(i,start,end,N);
			if(flag&&is_milked){
				count++;
			}else if(!flag&&is_milked){
				flag=true;
				if(max_idle<count){
					max_idle=count;
				}
				//---------
				count=1;
			}else if(flag&&!is_milked){
				flag=false;
				if(max_milked<count){
					max_milked=count;
				}
				count=1;
			}else{
				count++;
			}
		}
		
		
		out.println(Integer.toString(max_milked)+" "+Integer.toString(max_idle));
	    out.close();
	}
	
	public static boolean isMilked(int t,List<Integer> start,List<Integer>end,int N){
    	boolean flag=false;
    	for(int i=0;i<N;i++){
    		if(t>=start.get(i)&&t<end.get(i)){
    			return true;
    		}else{
    			
    		}
    	}
    	return flag;
    }
}
