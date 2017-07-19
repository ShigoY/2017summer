/*
ID: lcoder1
LANG: JAVA
TASK: namenum
 */

import java.io.*;
import java.util.*;

class namenum {

	public static String process(String source){
		String temp=source;
		for(int i=0;i<source.length();i++){
			temp=temp.replace(source.charAt(i),set_replace(source.charAt(i)));
		}
		return temp;
	}
	public static char set_replace(char a){
		switch(a){
		case 'A':case 'B':case 'C':return '2';
		case 'D':case 'E':case 'F':return '3';
		case 'G':case 'H':case 'I':return '4';
		case 'J':case 'K':case 'L':return '5';
		case 'M':case 'N':case 'O':return '6';
		case 'P':case 'R':case 'S':return '7';
		case 'T':case 'U':case 'V':return '8';
		case 'W':case 'X':case 'Y':return '9';
		default:return a;
		}
	}
	
	public static void main(String[] args) throws IOException {
		// TODO Auto-generated method stub
		BufferedReader f=new BufferedReader(new FileReader("namenum.in"));
		BufferedReader d=new BufferedReader(new FileReader("dict.txt"));
		PrintWriter out=new PrintWriter(new BufferedWriter(new FileWriter("namenum.out")));
		List<String> dict=new ArrayList<String> ();
		String str=d.readLine();
		
		while(str!=null){
			dict.add(str);
			str=d.readLine();
		}
		
		String nums=f.readLine();
		boolean flag=false;
		for(String s:dict){
			String to_num=process(new String(s));
			if(nums.equals(to_num)){
				flag=true;
				out.println(s);
			}
		}
		if(!flag){
			out.println("NONE");
		}
		out.close();
	}
		
}

