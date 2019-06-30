#! /usr/bin/env python   
# -*- coding: utf-8 -*-

#
# Deskolemization script for FIMO
#
# Orkunt Sabuncu
#

import sys
import re
import xml.etree.cElementTree as ElementTree
from optparse import OptionParser
from optparse import OptionValueError

options = None
output = sys.stdout

# eprover
SKOLEM_PTRN = re.compile(r'esk\d+_\d+')
# vampire
#SKOLEM_PTRN = re.compile(r'sK\d+')

# absence of rootnode means it has already been printed out
clauses = dict() # name-> [(eliminate,sko),rootnode,setoflistsrepr]

# all the rest of the clause where skolem function is included
skolem2clause = dict() # (skoname,arity)-> [deskolemizable,setoflistrepr,[(clausename,prednode,predrepr)]]

clause_status = dict()

def dumpXML(root,out):
  #if root.tag == 'formula':   
  if root.tag == 'predicate':
    if len(out)>0 and out[-1] == ['~']:
      out[-1].append(root.get('name'))
    else:
      out.append([root.get('name')])
      
  #elif root.tag == 'disjunction':
    #for e in root.findall('*'):
      #dumpXML(e,out)
      
  elif root.tag == 'negation':
    out.append(['~'])
    
  elif root.tag == 'function':
    out[-1].append(root.get('name'))
    
  elif root.tag == 'variable':
    out[-1].append('__var_'+root.get('name'))
    
  for e in root.findall('*'):
    dumpXML(e,out)

in_negation = False

def outputDeskolemizedClause(root,pred,skoname,level):
  global in_negation
  
  # watch out pred is actually a list of root nodes of predicates
  #if root == pred:
  if root in pred:
    return
    
  if root.tag == 'formula':
    output.write('cnf(%s,%s,(\n' %(root.get('name'),clause_status[root.get('name')]))
    for e in root.findall('*'):
      outputDeskolemizedClause(e,pred,skoname,level)
      
  elif root.tag == 'predicate':
    if not root:        # propositional
      if in_negation:
        output.write('    ~ ')
      else:
        output.write('    ')
      output.write('%s |\n' %(root.get('name')))
    elif root.get('name') == '=':
      output.write('    ')
      i = 0
      for e in root.findall('*'):
        outputDeskolemizedClause(e,pred,skoname,0)
        i += 1
        if i == 1:
          if in_negation:
            output.write(' != ')
          else:
            output.write(' = ')
      output.write(' |\n')
    else:
      if in_negation:
        output.write('    ~ ')
      else:
        output.write('    ')
      output.write('%s(' %(root.get('name')))
      arity = len(root)
      i = 0
      for e in root.findall('*'):
        outputDeskolemizedClause(e,pred,skoname,arity-i)
        i += 1
      output.write(' |\n')
      
  elif root.tag == 'negation':
    #output.write('    ~ ')
    in_negation = True
    for e in root.findall('*'):
      outputDeskolemizedClause(e,pred,skoname,level)
    in_negation = False
      
  elif root.tag == 'function':
    if not root:
      output.write('%s' %(root.get('name')))
      if level > 1:
        output.write(',')
      elif  level != 0:
        output.write(')')
    else:
      output.write('%s(' %(root.get('name')))
      arity = len(root)
      i = 0
      for e in root.findall('*'):
        outputDeskolemizedClause(e,pred,skoname,arity-i)
        i += 1
      if level > 1:
        output.write(',')
      elif level != 0:
        output.write(')')
        
  elif root.tag == 'variable':
    output.write('%s' %(root.get('name')))
    if level > 1:
      output.write(',')
    elif level != 0:
      output.write(')')
  
  else:
    for e in root.findall('*'):
      outputDeskolemizedClause(e,pred,skoname,level)
 
def outputSkolemLiteral(root,skoname,level):
  global in_negation
  
  if root.tag == 'predicate':
    if root.get('name') == '=':
      #output.write('\t')
      i = 0
      for e in root.findall('*'):
        outputSkolemLiteral(e,skoname,0)
        i += 1
        if i == 1:
          if in_negation:
            output.write(' != ')
          else:
            output.write(' = ')
      #output.write(' &\n')
    else:
      if in_negation:
        #output.write('\t~ ')
        output.write('~ ')
      else:
        #output.write('\t')
        output.write('')
      output.write('%s(' %(root.get('name')))
      arity = len(root)
      i = 0
      for e in root.findall('*'):
        outputSkolemLiteral(e,skoname,arity-i)
        i += 1
      #output.write(' &\n')
      
  elif root.tag == 'negation':
    #output.write('    ~ ')
    in_negation = True
    for e in root.findall('*'):
      outputSkolemLiteral(e,skoname,level)
    in_negation = False
      
  elif root.tag == 'function':
    if skoname == (root.get('name'),len(root)):
      output.write('Y'+skoname[0])
      if level > 1:
        output.write(',')
      elif level != 0:
        output.write(')')
    elif not root:
      output.write('%s' %(root.get('name')))
      if level > 1:
        output.write(',')
      elif level != 0:
        output.write(')')
    else:
      output.write('%s(' %(root.get('name')))
      arity = len(root)
      i = 0
      for e in root.findall('*'):
        outputSkolemLiteral(e,skoname,arity-i)
        i += 1
      if level > 1:
        output.write(',')
      elif level != 0:
        output.write(')')
        
  elif root.tag == 'variable':
    output.write('%s' %(root.get('name')))
    if level > 1:
      output.write(',')
    elif level != 0:
      output.write(')')
  
  else:
    for e in root.findall('*'):
      outputSkolemLiteral(e,skoname,level)

def outputClauses():
  for cla in clauses:
    if not clauses[cla][0][0]:  # not eliminated
      tstp_formula = clauses[cla][1].find('tstp-logic-formula').text
      output.write('cnf(%s,%s,(%s)).\n' %(cla,clause_status[cla],tstp_formula))
    else:
      # find the predicate
      sko = clauses[cla][0][1]
      #pred = None
      #for i in skolem2clause[sko][2]:
        #if i[0] == cla:
          #pred = i[1]
          #break
      # find the preds with the sko in this clause
      for (clsname,predlist) in skolem2clause[sko][2]:
        if clsname == cla:
          preds = [predelem[0] for predelem in predlist]
          break
      outputDeskolemizedClause(clauses[cla][1],preds,sko,0)
      # output skolem predicates in existential quantifier
      output.write('    ? [Y%s]: (\n'%(sko[0]))
      
      # output for each clause the preds (disjunction)
      for (clsname,predlist) in skolem2clause[sko][2]:
        output.write('\t(  ')
        for p in predlist:
          outputSkolemLiteral(p[0],sko,0)
          if predlist.index(p) != len(predlist)-1:
            output.write(' | ');
        output.write('  )')
        if skolem2clause[sko][2].index((clsname,predlist)) != len(skolem2clause[sko][2])-1:
          output.write(' &\n')
      output.write(' ) )).\n')
          
      #lst = [x[1] for x in skolem2clause[sko][2]]
      #for l in lst:
        #outputSkolemLiteral(l,sko,0)
        #if lst.index(l) != len(lst)-1:
          #output.write(' &\n')
      #output.write(') )).\n')
     
def parseFormulaXML(root):
  
  if root.tag == 'formula':
    parent_map = dict((c, p) for p in root.getiterator() for c in p)
    
    clauses[root.get('name')] = [(False,None),root]
    clause_status[root.get('name')] = root.get('status')
    tmp = []
    dumpXML(root,tmp)
    tmp = set([tuple(x) for x in tmp])
    clauses[root.get('name')].append(tmp)
    #ElementTree.dump(root)
    #print tmp
    skolems = set([])
      
    for e in root.findall('.//function'):
      if SKOLEM_PTRN.match(e.get('name')) == None or len(e)<1:
        continue
      
      #print 'DEBUG', 'Parsing for', e.get('name')
      if (e.get('name'),len(e)) in skolem2clause and not skolem2clause[(e.get('name'),len(e))][0]:
        continue
      
      skolems.add((e.get('name'),len(e)))
      # find the parent predicate
      prnt = parent_map[e]
      while prnt.tag != 'predicate':
        prnt = parent_map[prnt]
      if parent_map[prnt].tag == 'negation':
        prnt = parent_map[prnt]
      predrepr = []
      dumpXML(prnt,predrepr)
      #print 'DEBUG', 'in literal', predrepr

      if (e.get('name'),len(e)) not in skolem2clause:
        # newly encountered
        #skolem2clause[(e.get('name'),len(e))] = [True,tmp-set([tuple(x) for x in predrepr]),[(root.get('name'),prnt,predrepr[0])]]
        skolem2clause[(e.get('name'),len(e))] = [True,set(['_init_']),[(root.get('name'),[(prnt,predrepr[0])])]]
        
        #skolem2clause[(e.get('name'),len(e))].append(tmp-set(predrepr))
        #skolem2clause[(e.get('name'),len(e))].append([predrepr])
      elif skolem2clause[(e.get('name'),len(e))][0]: # still deskolemizable
        # check first if the clause has already been processed i.e., it is a clause with 
        # two or more occurrence of the same skolem function
        appended = False
        for c in skolem2clause[(e.get('name'),len(e))][2]:
          if c[0] == root.get('name'):
            # append 
            # if not already appended. this is the case when skolem function occurs twice in the same predicate
            if not (prnt,predrepr[0]) in c[1]:
	      c[1].append((prnt,predrepr[0]))
            # remove it from the remaining clause
            #skolem2clause[(e.get('name'),len(e))][1].remove(tuple(predrepr[0]))
            appended = True
            break
        if appended:
          continue
        # inside a new (unprocessed clause)
        #elif tmp-set([tuple(x) for x in predrepr]) == skolem2clause[(e.get('name'),len(e))][1]:
        else:
          skolem2clause[(e.get('name'),len(e))][2].append((root.get('name'),[(prnt,predrepr[0])]))
          
        # OLD
        #if tmp-set([tuple(x) for x in predrepr]) == skolem2clause[(e.get('name'),len(e))][1]:
          #doappend = True
          #for c in skolem2clause[(e.get('name'),len(e))][2]:
            #if c[0] == root.get('name'):
              #doappend = False
              #if c[1] != prnt:
                #sys.stderr.write('Skolem function %s in two predicates in the same clause %s\n'%(e.get('name'),root.get('name')))
          #if doappend:
            #skolem2clause[(e.get('name'),len(e))][2].append((root.get('name'),prnt,predrepr[0]))
          #continue
        #else:
          #print 'DEBUG', e.get('name'), 'in', root.get('name'), 'caused non-deskolemizable'
          #print 'DEBUG', 'remaining was', skolem2clause[(e.get('name'),len(e))][1]
          ## make it not deskolemizable
          #skolem2clause[(e.get('name'),len(e))][0] = False
          #skolem2clause[(e.get('name'),len(e))][1] = None
          #skolem2clause[(e.get('name'),len(e))][2] = None
          #continue
    
    for sko in skolems:
      #print '\nDEBUG', 'end of clause', root.get('name'), 'checking', sko, skolem2clause[sko]
      if not skolem2clause[sko][0]:
	continue
      remainingcls = tmp.copy()
      for c in skolem2clause[sko][2]:
        if c[0] == root.get('name'):
	  #prednodes = set([])
          for p in c[1]:
	    #if p[0] in prednodes:
	      ## skolem function occurs twice in the same predicate
	      #print 'DEBUG', 'skolem function',sko, 'occurs twice in a predicate'
	      #continue
            remainingcls.remove(tuple(p[1]))
            #prednodes.add(p[0])
      if skolem2clause[sko][1] == set(['_init_']):
        skolem2clause[sko][1].remove('_init_')
        skolem2clause[sko][1] |= remainingcls
      elif not skolem2clause[sko][1] == remainingcls:
        #it is still deskolemizable
        #print 'DEBUG', sko, 'in', root.get('name'), 'caused non-deskolemizable'
        #print 'DEBUG', 'remaining was', skolem2clause[sko][1]
        # make it not deskolemizable
        skolem2clause[sko][0] = False
        skolem2clause[sko][1] = None
        skolem2clause[sko][2] = None
        
    

def main():
  global options
  global output
  
  parser = OptionParser()
  (options,args) = parser.parse_args()
  
  if len(args) == 0 :
    input = sys.stdin
  else:
    input = open(args[0])
    
  try:
    root = ElementTree.parse(input)
  except:
    output.write('ERROR PROPAGATION IN OUTPUT\n')
    raise
  
  for elem in root.findall('formula'):
    #output = sys.stdout
    parseFormulaXML(elem)
  
  # now decide which clauses should be eliminated
  # first sort the skolem functions
  skolems = [x for x in skolem2clause]
  skolems.sort(lambda x,y: cmp(x[1],y[1]))
  skolems.reverse()
  for sko in skolems:
    #print 'DEBUG', 'checking for', sko
    donteliminate = False
    if skolem2clause[sko][0]:   # can be deskolemizable
      clas = [x[0] for x in skolem2clause[sko][2]]
      for cla in clas:
        #print 'DEBUG', 'checking its clauses', cla
        if cla not in clauses or clauses[cla][0][0]:     # already eliminated
          #print 'DEBUG', 'eliminated'
          skolem2clause[sko][0] = False
          donteliminate = True
          break
      #check for free variables in predicates with skolem function
      remaining_cla_vars = set(filter(lambda a: a[:6]=='__var_', [v for l in skolem2clause[sko][1] for v in l]))
      #print 'DEBUG', 'remaining clause vars', remaining_cla_vars
      # OLD: for (clsname,elem,pred) in skolem2clause[sko][2]:
      for (clsname,predlist) in skolem2clause[sko][2]:
        pred_vars = set([])
        for (elem,pred) in predlist:
          pred_vars |= set(filter(lambda a: a[:6]=='__var_', pred))
        #print 'DEBUG', 'pred vars', pred_vars
        if not pred_vars <= remaining_cla_vars:
          #print 'DEBUG', sko, 'in', clsname, 'not eliminated because of universal variables'
          skolem2clause[sko][0] = False
          donteliminate = True
          break
      if donteliminate:
        continue
      #print 'DEBUG', 'setting deskolemized clause', clas[0]
      clauses[clas[0]][0] = (True,sko)
      for cla in clas[1:]:
        #print 'DEBUG', 'deleting', cla
        del clauses[cla]
        #clauses[cla][0] = (True,sko)
  
  
  # debug outputs
  #print clauses
  #print skolem2clause
  #for (sko,lst) in skolem2clause.items():
    #if not lst[0]:
      #print sko, lst
    #else:
      #print sko, lst[0]
      #print 'remaining clause:', lst[1]
      #print 'predicates:', lst[2]
      
  #print '---'
  #for (name,clause) in clauses.items():
    #if not clause[0][0]:
      #print name
    #else:
      #print name, clause[0], clause[1]
      #print 'list representation:', clause[2]
      
  outputClauses()
  

if __name__ == "__main__":
  main()