import sys
import clingo
import  puzzle_board
import time
import datetime
from clingo import SolveResult,Function,Control,Model
from sys import stdout

class Solver:

    def __init__(self, board):
        self.instance_str = ''
        self.board = board
        self.new_filename=''

    def on_model(self, model):
        for term in model.symbols(self,terms=True):
            print term




    def set_instance(self):
        for i in range(self.board.get_grid_dim()):
            for j in range(self.board.get_grid_dim()):
                pos=j+1+i*self.board.get_grid_dim()
                value=self.board.get_tile(i,j)
                self.instance_str += 'init('+str(pos)+','+str(value)+').'
                self.instance_str += '\n'
        self.new_filename='15puzzle_inst_'+time.strftime("%b%d%Y%H%M%S", time.localtime())+'.lp'
        out=open(self.new_filename,'w')
        #out.write("#program base.\n")
        out.write(self.instance_str)
        out.close()

    def get_result(self):
        pass

    def solve_instance(self):
        prg=Control()

        prg.load("puzzle15.lp")
        prg.load(self.new_filename)
        ret, parts, step = SolveResult.unsatisfiable, [], 1
        parts.append(("base", []))
        while ret==SolveResult.unsatisfiable:
            parts.append(("step", [step]))
            parts.append(("check", [step]))
            prg.ground(parts)
            prg.release_external(Function("query", [step - 1]))
            prg.assign_external(Function("query", [step]), True)
            #f = lambda m: stdout.write(str(m)+'\n')
            print("step:"+str(step)+" Solving...")
            ret, parts, step = prg.solve(on_model=self.on_model), [] , step + 1
            if ret.__repr__()=='UNSAT':
                ret=SolveResult.unsatisfiable
            else:
                ret=SolveResult.satisfiable

