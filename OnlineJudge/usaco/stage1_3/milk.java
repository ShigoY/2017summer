/*
ID: l_coder1
LANG: JAVA
TASK: milk
 */

//package stage1_3;
import java.util.*;
import java.io.*;


class milk {
	
	public static void main(String[] args) throws IOException {
		
		class Infos{
			private int price;
			private int amount;
			public Infos(int price,int amount){
				this.price=price;
				this.amount=amount;
			}
			
			public void set_price(int price){
				this.price=price;
			}
			
			public void set_amount(int amount){
				this.amount=amount;
			}
			
			public int get_price(){
				return this.price;
			}
			
			public int get_amount(){
				return this.amount;
			}
		}
		
		class SortByPrice implements Comparator<Infos>{

			@Override
			public int compare(Infos inf1, Infos inf2) {
				// TODO Auto-generated method stub
				if(inf1.get_price()==inf2.get_price()){
					return 0;
				}else if(inf1.get_price()>inf2.get_price()){
					return 1;
				}else{
					return -1;
				}
			}
			
		}
		
		// TODO Auto-generated method stub
		BufferedReader f=new BufferedReader(new FileReader("milk.in"));
		PrintWriter out=new PrintWriter(new BufferedWriter(new FileWriter("milk.out")));
		StringTokenizer st=new StringTokenizer(f.readLine());
		int N=Integer.parseInt(st.nextToken());
		int M=Integer.parseInt(st.nextToken());
		List<Infos> infs=new ArrayList<Infos> ();
		
		for(int i=0;i<M;i++){
			StringTokenizer tk=new StringTokenizer(f.readLine());
			int price=Integer.parseInt(tk.nextToken());
			int amount=Integer.parseInt(tk.nextToken());
			Infos inf=new Infos(price,amount);
			infs.add(inf);
		}
		
		Collections.sort(infs, new SortByPrice());
		
		int total=0;
		int all=0;
		int i=0;
		while(all<N&&i<M){
			int price=infs.get(i).get_price();
			int amount=infs.get(i).get_amount();
			if(all+amount>=N){
				total+=(N-all)*price;
				break;
			}else{
				total+=price*amount;
				all+=amount;
			}
			i++;
		}
		
		out.println(total);
		out.close();
	}

}
