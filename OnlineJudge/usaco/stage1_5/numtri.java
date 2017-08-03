/*
ID:l_coder1
LANG:JAVA
TASK:numtri
*/
//package stage1_5;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.StringTokenizer;

public class numtri {
	final static int MAX=1000;
	final static int INF=100000;
	private static int N;
	private static int[][] tri;
	private static PrintWriter out;
	
	//Dynamic programming
	public static void DP(){
		int[][] dist=new int[MAX][MAX];
		dist[0][0]=tri[0][0];
		for(int i=1;i<N;i++){
			for(int j=0;j<=i;j++){
				if(j>0&&j<i){
					//two parent
					int d1=dist[i-1][j-1]+tri[i][j];
					int d2=dist[i-1][j]+tri[i][j];
					if(d1<d2){
						dist[i][j]=d2;
					}else{
						dist[i][j]=d1;
					}
				}else if(j==0){
					//only one right parent(left child)
					dist[i][j]=dist[i-1][j]+tri[i][j];
				}else if(j==i){
					//only one left parent
					dist[i][j]=dist[i-1][j-1]+tri[i][j];
				}else{
					
				}
			}
		}
		
		int max=0;
		for(int i=0;i<N;i++){
			if(dist[N-1][i]>=max){
				max=dist[N-1][i];
			}
		}
		out.println(Integer.toString(max));
	}
	
	public static void main(String[] args) throws IOException{
		// TODO Auto-generated method stub
		BufferedReader f=new BufferedReader(new FileReader("numtri.in"));
		out=new PrintWriter(new BufferedWriter(new FileWriter("numtri.out")));
		N=Integer.parseInt((new StringTokenizer(f.readLine())).nextToken());
		tri=new int[MAX][MAX];
		for(int i=0;i<N;i++){
			StringTokenizer s=new StringTokenizer(f.readLine());
			for(int j=0;j<=i;j++){
				tri[i][j]=Integer.parseInt(s.nextToken());
			}
		}
		DP();
		out.close();
	}

}
