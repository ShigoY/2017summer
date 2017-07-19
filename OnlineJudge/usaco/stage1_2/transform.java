/*
ID: lcoder1
LANG: JAVA
TASK: transform
 */
//package stage1_2;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.StringTokenizer;

class transform {

	public static void main(String[] args) throws IOException {
		// TODO Auto-generated method stub
		BufferedReader f=new BufferedReader(new FileReader("transform.in"));
		PrintWriter out=new PrintWriter(new BufferedWriter(new FileWriter("transform.out")));
		StringTokenizer st1=new StringTokenizer(f.readLine());
		int N=Integer.parseInt(st1.nextToken());
		String str="";
		char [][]a1=new char[10][10];
		for(int i=0;i<N;i++){
			StringBuffer s=new StringBuffer(f.readLine());
			for(int j=0;j<N;j++){
				
				a1[i][j]=s.charAt(j);
			}
		}
		
		char [][]a2=new char[10][10];
		for(int i=0;i<N;i++){
			StringBuffer s=new StringBuffer(f.readLine());
			for(int j=0;j<N;j++){
				a2[i][j]=s.charAt(j);
			}
		}
		
		
		if(comp(a2,trans1(a1,N),N)){
			str="1";
		}else if(comp(a2,trans2(a1,N),N)){
			str="2";
		}else if(comp(a2,trans3(a1,N),N)){
			str="3";
		}else if(comp(a2,trans4(a1,N),N)){
			str="4";
		}else if(comp(a2,trans5_1(a1,N),N)){
			str="5";
		}else if(comp(a2,trans5_2(a1,N),N)){
			str="5";
		}else if(comp(a2,trans5_3(a1,N),N)){
			str="5";
		}else if(comp(a2,trans6(a1,N),N)){
			str="6";
		}else{
			str="7";
		}
		
		out.println(str);
		out.close();
	}
	//clockwise 90 degree
	public static char[][] trans1(char [][]a,int N){
		char [][] temp=new char[10][10];
		for(int i=0;i<N;i++){
			for(int j=0;j<N;j++){
				temp[i][j]=a[j][N-1-i];
			}
		}

		return temp;
	}
	//clockwise 180
	public static char[][] trans2(char [][]a,int N){
		char [][] temp=new char[10][10];
		for(int i=0;i<N;i++){
			for(int j=0;j<N;j++){
				temp[i][j]=a[N-1-i][N-1-j];
			}
		}
		return temp;
	}
	//clockwise 270
	public static char[][] trans3(char [][]a,int N){
		char [][] temp=new char [10][10];
		for(int i=0;i<N;i++){
			for(int j=0;j<N;j++){
				temp[i][j]=a[N-1-j][i];
			}
		}
		return temp;
	}
	//Relfection
	public static char[][] trans4(char [][]a,int N){
		char [][] temp=new char[10][10];
		for(int i=0;i<N;i++){
			for(int j=0;j<N;j++){
				temp[i][j]=a[i][N-j-1];
			}
		}
		return temp;
	}
	//Combination
	public static char[][] trans5_1(char [][]a,int N){
		char [][] temp1=trans4(a,N);
		char [][] temp2=trans1(temp1,N);
		return temp2;
		
	}
	
	public static char[][] trans5_2(char [][]a,int N){
		char [][] temp1=trans4(a,N);
		char [][] temp2=trans2(temp1,N);
		return temp2;
	}
	
	public static char[][] trans5_3(char [][]a,int N){
		char [][] temp1=trans4(a,N);
		char [][] temp2=trans3(temp1,N);
		return temp2;
	}
	
	public static char[][] trans6(char [][]a,int N){
		return a;
	}
	
	public static boolean comp(char [][]a,char [][]b,int N){
		boolean flag=true;
		for(int i=0;i<N;i++){
			for(int j=0;j<N;j++){
				if(a[i][j]!=b[i][j]){
					return false;
				}
			}
		}
		return flag;
	}
	
	public static void print(char a[][],int N){
		for(int i=0;i<N;i++){
			for(int j=0;j<N;j++){
				System.out.print(a[i][j]);
			}
			System.out.println();
		}
	}

}
