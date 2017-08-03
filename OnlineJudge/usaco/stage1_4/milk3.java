/*
 ID:l_coder1
 LANG:JAVA
 TASK:milk3
 */

//package stage1_4;

import java.io.*;
import java.util.StringTokenizer;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

public class milk3 {
	
	private static int la;
	private static int lb;
	private static int lc;
	private static Queue<Triple> queue;
	private static int v[][][];
	private static PrintWriter out;
	private static List<Integer> li;
	
	
	public static void main(String[] args) throws IOException {
		// TODO Auto-generated method stub
		BufferedReader f=new BufferedReader(new FileReader("milk3.in"));
		out=new PrintWriter(new BufferedWriter(new FileWriter("milk3.out")));
		StringTokenizer s=new StringTokenizer(f.readLine());
		la=Integer.parseInt(s.nextToken());
		lb=Integer.parseInt(s.nextToken());
		lc=Integer.parseInt(s.nextToken());
		queue=new LinkedList<Triple>();
		v=new int[22][22][22];
		li=new ArrayList<Integer> ();
		queue.add(new Triple(0,0,lc));
		BFS();
		Collections.sort(li);
		for(int i=0;i<li.size();i++){
			out.print(Integer.toString(li.get(i)));
			if(i!=li.size()-1){
				out.print(" ");
			}else{
				out.println();
			}
		}
		out.close();
		
	}
	
	public static void extend(int a,int b,int c,int mode){
		int na=a,nb=b,nc=c;
		boolean flag=false;
		if(mode==1){
			//a->b
			if(a!=0&&b!=lb){
				if(a+b<lb){
					na=0;nb=a+b;
				}else{
					na=a+b-lb;nb=lb;
				}
				flag=true;
			}
		}else if(mode==2){
			//a->c
			if(a!=0&&c!=lc){
				if(a+c<lc){
					na=0;nc=a+c;
				}else{
					na=a+c-lc;nc=lc;
				}
				flag=true;
			}
		}else if(mode==3){
			//b->c
			if(b!=0&&c!=lc){
				if(b+c<lc){
					nb=0;nc=b+c;
				}else{
					nb=b+c-lc;nc=lc;
				}
				flag=true;
			}
		}else if(mode==4){
			//b->a
			if(b!=0&&a!=la){
				if(b+a<la){
					nb=0;na=b+a;
				}else{
					nb=b+a-la;na=la;
				}
				flag=true;
			}
		}else if(mode==5){
			//c->a
			if(c!=0&&a!=la){
				if(c+a<la){
					nc=0;na=c+a;
				}else{
					nc=c+a-la;na=la;
				}
				flag=true;
			}
		}else if(mode==6){
			//c->b
			if(c!=0&&b!=lb){
				if(c+b<lb){
					nc=0;nb=c+b;
				}else{
					nc=c+b-lb;nb=lb;
				}
				flag=true;
			}
		}else{
			
		}
		if(flag){
			Triple n=new Triple(na,nb,nc);
			queue.add(n);
		}
	}
	
	public static void BFS(){
		while(!queue.isEmpty()){
			Triple curr=queue.poll();
			
			int a=curr.getA();
			int b=curr.getB();
			int c=curr.getC();
			if(v[a][b][c]!=0){
				//has been visited
			}else{
				v[a][b][c]=1;
				if(a==0){
					li.add(c);
				}
				//extend child nodes
				for(int i=1;i<7;i++){
					extend(a,b,c,i);
				}
				
			}
		}
	}

}

class Triple{
	private int a;
	private int b;
	private int c;
	
	public Triple(int a,int b,int c){
		this.a=a;
		this.b=b;
		this.c=c;
	}
	
	public int getA() {
		return a;
	}
	public void setA(int a) {
		this.a = a;
	}
	public int getB() {
		return b;
	}
	public void setB(int b) {
		this.b = b;
	}
	public int getC() {
		return c;
	}
	public void setC(int c) {
		this.c = c;
	}
	
}
