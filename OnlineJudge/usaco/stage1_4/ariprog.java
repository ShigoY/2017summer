/*
  ID:l_coder1
  LANG:JAVA
  TASK:ariprog
*/

//package stage1_4;
import java.awt.Point;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.StringTokenizer;


public class ariprog {

	final static int MAX=125001;
	static int M;
	static int N;
	public static List<Point> l=new ArrayList<Point>();
//	public static boolean isIn(int []a,int N,int p){
//		for(int i=0;i<N;i++){
//			if(a[i]==p){
//				return true;
//			}
//		}
//		return false;
//	}
	public static void dfs(int []a,int ct,int start,int gap){
		if(ct==N){
			Point p=new Point(start-(N-1)*gap,gap);
			l.add(p);
			return;
		}
		if(a[start+gap]==1){
			ct++;
			dfs(a,ct,start+gap,gap);
		}else{
			return;
		}
	}
	
	
	
	public static void main(String[] args) throws IOException {
		// TODO Auto-generated method stub
		BufferedReader f=new BufferedReader(new FileReader("ariprog.in"));
		PrintWriter out=new PrintWriter(new BufferedWriter(new FileWriter("ariprog.out")));
		N=Integer.parseInt((new StringTokenizer(f.readLine())).nextToken());
		M=Integer.parseInt((new StringTokenizer(f.readLine())).nextToken());
		//---logic---
		int []a=new int[MAX];
		for(int i=0;i<=M;i++){
			for(int j=i;j<=M;j++){
					a[i*i+j*j]=1;
			}
		}
				
		for(int i=0;i<=2*M*M;i++){
			for(int j=1;j<=(2*M*M-i)/(N-1);j++){
				if(a[i]==1){
					dfs(a,1,i,j);
				}
			}
		}
		
		
		if(!l.isEmpty()){
			Collections.sort(l,new tAComp());
			for(Point p:l){
				int x=(new Double(p.getX())).intValue();
				int y=(new Double(p.getY())).intValue();
				out.println(x+" "+y);
			}
		}else{
			out.println("NONE");
		}
		out.close();
	}
	

	

}

class tAComp implements Comparator<Point>{
	@Override
	public int compare(Point p1, Point p2) {
		if(p1.getY()>p2.getY()){
			return 1;
		}else if(p1.getY()<p2.getY()){
			return -1;
		}else{
			if(p1.getX()>p2.getX()){
				return 1;
			}else if(p1.getX()<p2.getX()){
				return -1;
			}else{
				return 0;
			}
		}
	}

}

