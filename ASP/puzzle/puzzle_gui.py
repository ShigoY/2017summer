import sys
import puzzle_board
import solver
import time
from puzzle_board import Board
from solver import Solver
from PyQt5.QtWidgets import QWidget,QApplication,QMainWindow,QPushButton,QMessageBox,QVBoxLayout,QHBoxLayout,QFrame
from PyQt5.QtGui import QPainter,QColor,QFont,QPen
from PyQt5.QtCore import Qt,pyqtSlot,QPoint

class GUI(QMainWindow):
    def __init__(self,board):
        super(GUI, self).__init__()
        self.board=board
        self.topX=500
        self.topY=500
        self.iWidth=800
        self.iHeight=500
        self.result=[]
        self.init_ui()

    def init_ui(self):


        button0=QPushButton('generate',self)
        button0.clicked.connect(self.on_click)
        button1=QPushButton('Display',self)
        button1.clicked.connect(self.on_display)
        mainLayout=QHBoxLayout()

        canvasLayout=QVBoxLayout()
        controllerLayout=QVBoxLayout()

        self.canvas=PaintArea(self.board,self.iHeight/4)

        canvasLayout.addWidget(self.canvas)

        controllerLayout.addWidget(button0)
        controllerLayout.addWidget(button1)

        mainLayout.addLayout(canvasLayout,1)
        mainLayout.addLayout(controllerLayout,1)

        self.setCentralWidget(QWidget(self))
        self.centralWidget().setLayout(mainLayout)

        self.setWindowTitle('15Puzzle')

        self.setGeometry(self.topX, self.topY, self.iWidth, self.iHeight)
        self.statusBar().showMessage('Message in status bar')
        self.setFocusPolicy(Qt.StrongFocus)
        self.show()

    def keyPressEvent(self, e):
        if e.key() == Qt.Key_Up:
            self.board.move([1,0])
            self.canvas.repaint()
            print('UP')

        elif e.key() == Qt.Key_Down:
            self.board.move([-1,0])
            self.canvas.repaint()
            print('Down')

        elif e.key() == Qt.Key_Left:
            self.board.move([0,1])
            self.canvas.repaint()
            print('left')

        elif e.key() == Qt.Key_Right:
            self.board.move([0,-1])
            self.canvas.repaint()
            print('right')

        else:
            print('Works')

    def draw_board(self,event):
        pass

    @pyqtSlot()
    def on_click(self):
       sol=Solver(self.board)
       sol.set_instance()
       sol.solve_instance()
       self.result=sol.get_solution()

    @pyqtSlot()
    def on_display(self):
        if len(self.result)==0:
            print 'Please solve the puzzle first!'
        else:
            for step in self.result:
                if step=='up':
                    self.board.move([-1,0])
                elif step=='down':
                    self.board.move([1,0])
                elif step=='left':
                    self.board.move([0,-1])
                else:
                    self.board.move([0,1])
                time.sleep(1)
                self.canvas.repaint()

        self.result=[]


    #def keydown:

    #def keyUp

    #def KeyLeft

    #def KeyRight

class PaintArea(QWidget):
    def __init__(self,board,width):
        super(PaintArea, self).__init__()
        self.board=board
        self.dim=board.grid_dim
        self.width=width/1.5
        #self.show()


    def paintEvent(self, event):
        qp=QPainter()

        qp.begin(self)
        #qp.drawText(event.rect(), Qt.AlignCenter, 'Despacito')
        for i in range(self.dim):
            for j in range(self.dim):
                #draw the board
                num=self.board.get_tile(i,j)
                qp.drawRect((self.width+10)*j,(self.width+10)*i,self.width,self.width)
                if num==0:
                    color=Qt.white
                else:
                    color=Qt.blue
                qp.fillRect((self.width+10)*j,(self.width+10)*i,self.width,self.width,color)
                qp.setFont(QFont("Arial",30))
                qp.drawText(QPoint((self.width+10)*j+self.width/2-30,(self.width+10)*i+self.width/2+10),str(num))
        qp.end()



if __name__=='__main__':
    board=Board(4)
    app=QApplication(sys.argv)
    ex=GUI(board)
    sys.exit(app.exec_())