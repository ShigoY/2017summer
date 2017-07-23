/*
 ID:l_coder1
 LANG:JAVA
 TASK:wormhole
 */
//package stage1_3;
//Level difficult! 
//Bellmann Ford to detect whether there exist a minus ring or not
//20:46


import java.awt.Point;
import java.io.*;
import java.util.*;
public class wormhole {

	private static List<Point> lp;
	private static int N;
	private final static int MAX=14;
	private final static int INF=100;
	private static int count=0;
	private static boolean flag;
	private static int []p;
	
	public static void main(String[] args) throws IOException {
		
		// TODO Auto-generated method stub
		BufferedReader f=new BufferedReader(new FileReader("wormhole.in"));
		PrintWriter out=new PrintWriter(new BufferedWriter(new FileWriter("wormhole.out")));
		StringTokenizer sn=new StringTokenizer(f.readLine());
		N=Integer.parseInt(sn.nextToken());
		lp=new ArrayList<Point>();
		for(int i=0;i<N;i++){
			StringTokenizer s=new StringTokenizer(f.readLine());
			Point p=new Point(Integer.parseInt(s.nextToken()),Integer.parseInt(s.nextToken()));
			lp.add(p);
		}
		//sort the points
		Collections.sort(lp,new SortByXY());
		
		
		//Or propably!
		p=new int[MAX];
		for(int i=0;i<N;i++){
			p[i]=-1;
		}
		out.println(dfs());
		out.close();
		//dfs enumberation
		
	}
	
	
	public static int fac(int p){
		if(p==1){
			return 1;
		}
		return p*fac(p-1);
	}
	
	
//	public static int dfs(){
//		int i,total=0;
//		for(i=0;i<N;i++){
//			if(p[i]==-1){
//				break;
//			}
//		}
//		if(i==N){
//			if(check(p)){
//				return 1; 
//			}else{
//				return 0;
//			}
//		}
//		
//		for(int j=i+1;j<N;j++){
//			if(p[j]==-1){
//				p[i]=j;
//				p[j]=i;
//				total+=dfs();
//				p[i]=p[j]=-1;
//			}
//		}
//		return total;
//	}
	
	
	//inconnected? INF? PROBLEMATIC
	public static boolean check(int []p){
		for(int i=0;i<N;i++){
			flag=false;
			int pre=i;
			while(true){
				if(flag){
					if(p[pre]!=-1){
							pre=p[pre];
							flag=false;
					}
					if(flag){
						break;
					}
					
				}else{
					if(pre<N-1&&lp.get(pre).getY()==lp.get(pre+1).getY()){
						pre=pre+1;
						flag=true;
					}
					if(!flag){
						break;
					}
				}
				if(pre==i&&!flag){
					return true;
				}
			}
		}
		return false;
		
	}
				
}

class SortByXY implements Comparator<Point>{

	@Override
	public int compare(Point p1, Point p2) {
		if(p1.getY()==p2.getY()){
			if(p1.getX()<p2.getX()){
				return -1;
			}else if(p1.getX()==p2.getX()){
				return 0;
			}else{
				return 1;
			}
		}else if(p1.getY()<p2.getY()){
			return -1;
		}else{
			return 1;
		}
	}
}
