package stage1_3;

public class wh_test {
	
	public static final int MAX=4;
	public static int N=4;
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		
		int [][]st={{0,-1,1,1},{1,0,0,1},{1,1,0,-1},{0,1,1,0}};
		if(check(st)){
			System.out.println("True");
		}else{
			System.out.println("False");
		}
	}
	
	public static boolean check(int [][]p){
		//Bellmann-Ford
		int [][]dist=new int[MAX][MAX];
		for(int i=0;i<N;i++){
			for(int j=0;j<N;j++){
				dist[i][j]=p[i][j];
			}
		}
		
		//loose
		//You Silly Shit!
		for(int k=0;k<N;k++){
			for(int s=0;s<N;s++){
				for(int e=0;e<N;e++){
					if(p[s][e]>0){
						
					}else{
						for(int i=0;i<N;i++){
								if(dist[i][s]+p[s][e]<dist[i][e]){
									dist[i][e]=dist[i][s]+p[s][e];
								}
						}
					}
				}
			}
		}
	
		for(int i=0;i<N;i++){
			if(dist[i][i]>=0){
				print(dist);
				return false;
			}
		}
		return true;
	}
	
	public static void print(int [][]gs){
		for(int i=0;i<N;i++){
			for(int j=0;j<N;j++){
				System.out.print(gs[i][j]);
			}
			System.out.println();
		}
	}
	
}
