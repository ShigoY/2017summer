
class Board:

    def __init__(self,grid_dim):
        self.grid_dim = grid_dim
        self.reset()
    def reset(self):
        self.cells=[[i+1+j*self.grid_dim for i in range(self.grid_dim)]for j in range(self.grid_dim)]
        self.set_board(self.grid_dim-1,self.grid_dim-1,0)
        self.zero_pos=[self.grid_dim-1,self.grid_dim-1]
        pass

    def get_grid_dim(self):
        return self.grid_dim

    def set_board(self,row,col,value):
        self.cells[row][col]=value

    def get_tile(self,row,col):
        return self.cells[row][col]

    def move(self, direction):
        posX=self.zero_pos[0]+direction[0]
        posY=self.zero_pos[1]+direction[1]
        if 0<=posX<=self.grid_dim-1 and 0<=posY<=self.grid_dim-1:
            self.set_board(self.zero_pos[0],self.zero_pos[1],self.cells[posX][posY])
            self.set_board(posX,posY,0)
            self.zero_pos[0]=posX
            self.zero_pos[1]=posY
        else:
            pass

    def get_board(self):
        return self.cells
