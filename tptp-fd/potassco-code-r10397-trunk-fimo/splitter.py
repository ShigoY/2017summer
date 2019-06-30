#! /usr/bin/env python   
# -*- coding: utf-8 -*-

#
# Splitter script for FIMO
#
# Orkunt Sabuncu
#

import sys
import re
import xml.etree.cElementTree as ElementTree
from optparse import OptionParser
from optparse import OptionValueError
import subprocess
import shlex

CLSNAME_PTRN = re.compile('i_\d_(\d+)')

MAXVAR_PTRN = re.compile('maxvar\([^ ]+,(\d+),(\d+)\)')
CLSINANS_PTRN = re.compile('clause\(([^ ]+)\)')

# use group(1) and group(3) for the first and second arguments respectively CRAZY PATTERN!
#EQARGS_PTRN = re.compile(r'_eq\(([^(]+(\()?.+(?(2)\))),(.+)\)$')
EQARGS_PTRN = re.compile(r'_eq\((.+),_comma_,(.+)\)$')

VAR_PTRN = re.compile(r'_var([^,()]+)')

options = None
output = sys.stdout
inNegationContext = False
tstp_formula = ''

clause_name = None
ICLINGO_BIN = 'iclingo-banane'
#TODO the following path should come from command line
#SPLITTING_ENCODING_LP = '/home/orkunt/workplace/fmb/DeepTerms/newfmc2iasp/splitinc.lp'
#SPLITTING_ENCODING_LP = '/home/orkunt/workplace/fmb/DeepTerms/newfmc2iasp/splitinc2.lp'
SPLITTING_ENCODING = '''
% Clause splitting

#base.

clause(C) :- clause2pred(C,P).
clause2var(C,V) :- clause2pred(C,P), pred2var(P,V).
var2pred(C,V,P) :- pred2var(P,V), clause2pred(C,P).

numvars(C,N) :- clause(C), N := {clause2var(C,V):clause(C)}.
numpred(C,N) :- clause(C), N := {clause2pred(C,P):clause(C)}.

next(P1,P2) :- clause2pred(C,P1;P2), P1<P2, not clause2pred(C,PX):clause2pred(C,PX):P1<PX:PX<P2.
order(P,1) :- clause2pred(C,P), not next(PX,P):next(PX,P).
order(P,N+1) :- order(P1,N), next(P1,P).

#cumulative k.

comp(k).

%{ component(C,P,k) } :- clause2pred(C,P), not numvars(C,0).
{ component(C,P,k) } :- clause2pred(C,P), order(P,O), k<=O,  not numvars(C,0).

% components in components
{ component(C,X,k) } :- clause(C), comp(X), X<k.
{ component(C,k,X) } :- clause(C), comp(X), X<k.

in_comp(C,P,k) :- component(C,P,k), not comp(P).
in_comp(C,P,k) :- component(C,X,k), in_comp(C,P,X).


% for literals at most one component
%:- component(C,P,X), component(C,P,k), X<k.
%:- component(C,P,X), component(C,P,k), X<k, not comp(P).
:- component(C,P,X1), component(C,P,X2), X1<X2, not comp(P).

compvars(C,k,V) :- component(C,P,k), pred2var(P,V).
compvars(C,k,V) :- component(C,X,k), comp(X), compoutputs(C,X,V).
%compcloses(C,k,V) :- compvars(C,k,V), component(C,P,k):var2pred(C,V,P).
compcloses(C,k,V) :- clause2var(C,V), in_comp(C,P,k):var2pred(C,V,P).
compoutputs(C,k,V) :- compvars(C,k,V), not compcloses(C,k,V).

compvarcount(C,k,N) :- clause(C), N = { compvars(C,k,V):clause2var(C,V) }.
:- compvarcount(C,k,0).

%:- maxvar(C,N,k), maxvar(C,N1,k-1), N>=N1.

#volatile k.

% every predicate should be in at least one component
:- clause2pred(C,P), { component(C,P,X):comp(X) } 0.

% components should close all the variables i.e. it is a valid split
:- clause2var(C,V), { compcloses(C,X,V):comp(X) } 0.

maxvar(C,N,k) :- clause(C), N = #max [ compvarcount(C,X,O1)=O1 ].

:-maxvar(C,N,k), numvars(C,NV), N>=NV-k+2.

#hide clause2pred/2.
#hide pred2var/2.
#hide clause2var/2.
#hide var2pred/3.
'''

clause_status = dict()

def processAnswerSet(answerset):
  # find  how many components/splits there are
  tmpres = MAXVAR_PTRN.search(answerset)
  numofsplits = int(tmpres.group(2))
  numofmaxvars = int(tmpres.group(1))
  if numofsplits == 1:
    output.write('cnf(%s,%s,(%s)).\n' %(clause_name,clause_status[clause_name],tstp_formula))
    return
  
  #print numofsplits, numofmaxvars
  
  # clause name in answer set for convenience in regular expressions.
  clsinans = re.sub(r'([()])',r'[\1]',CLSINANS_PTRN.search(answerset).group(1))
  
  #print clsinans
  
  # compute split literals for each component except the last one
  # also initialize a list for keeping track of which components are used within the others
  iscompused = [False for i in xrange(1,numofsplits)]
  comppreds = []
  for i in xrange(1,numofsplits):
    outvars = re.findall('compoutputs\(%s,%d,_var([^ ]+)\)'%(clsinans,i), answerset)
    if len(outvars) == 0:
      comppreds.append('comp'+str(i)+'_'+clause_name)
    else:
      comppreds.append('comp'+str(i)+'_'+clause_name+'('+reduce(lambda x,y: x+','+y, outvars)+')')
  
  #print comppreds
  
  # prepare and output each split clause
  negative = False
  for i in xrange(1,numofsplits+1):
    complits = re.findall('component\(%s,([^ ]+),%d\)'%(clsinans,i), answerset)
    cnf_clause = 'cnf(%s_split%d,%s,( '%(clause_name,i,clause_status[clause_name])
    if i != numofsplits:
      cnf_clause += '%s | ' %(comppreds[i-1])
    for l in complits:
      # check whether literal is actually a component
      if l.isdigit():
	cnf_clause += '~%s | ' %(comppreds[int(l)-1])
	iscompused[int(l)-1] = True
	continue
      l = VAR_PTRN.sub(r'\1',l)
      if l[:4] == '_neg':
	negative = True
	l = l[5:-1]
      else:
	negative = False
      tmp = EQARGS_PTRN.match(l)
      if tmp:
	# equality literal
	if negative:
	  #cnf_clause += '%s!=%s | ' %(tmp.group(1),tmp.group(3))
	  cnf_clause += '%s!=%s | ' %(tmp.group(1),tmp.group(2))
	else:
	  #cnf_clause += '%s=%s | ' %(tmp.group(1),tmp.group(3))
	  cnf_clause += '%s=%s | ' %(tmp.group(1),tmp.group(2))
      else:
	if negative:
	  cnf_clause += '~%s | ' %(l)
	else:
	  cnf_clause += '%s | ' %(l)
    if i == numofsplits:
      # add the negation of unused split literals to the last split clause
      for j in xrange(1,numofsplits):
	if not iscompused[j-1]:
	  cnf_clause += '~%s | ' %(comppreds[j-1])
    cnf_clause =  cnf_clause[:-2] + ') ).\n'
    output.write(cnf_clause)
      
    #print complits
  

def parseFormulaXML(root):
  global clause_name
  global tstp_formula
  global output
  
  if root.tag == 'formula':
    clause_name = root.get('name')
    clause_status[root.get('name')] = root.get('status')
  
    output = sys.stdout
    output.write('\n%% clause %s\n' %(clause_name))
    
    # check whether we need to try splitting or not
    # if number of variables is less than 2, there won't be a split
    if len(set(map(lambda x: x.get('name'),root.findall('.//variable')))) < 2:
      tstp_formula = root.find('tstp-logic-formula').text
      output.write('cnf(%s,%s,(%s)).\n' %(clause_name,clause_status[clause_name],tstp_formula))
      return
      
    # we will call iclingo
    # change the output stream to input of the iclingo process
    #tmpfile = open('splittempinput','w')
    #output = tmpfile
    
    iclingo = subprocess.Popen([ICLINGO_BIN]+ shlex.split('--istop=UNSAT'), stdin=subprocess.PIPE, stderr=subprocess.PIPE, stdout=subprocess.PIPE)
    output = iclingo.stdin
 
    o = CLSNAME_PTRN.match(clause_name)
    old_clause_name = clause_name
    clause_name = '_c('+clause_name+','+o.group(1)+')'
    
    for e in root.findall('*'):
      parseFormulaXML(e)
    
    output.write(SPLITTING_ENCODING)
    output.close()
    
    # run iclingo run !
    output = sys.stdout
    #tmpfile.close()
    #iclingo = subprocess.Popen([ICLINGO_BIN,'--istop=UNSAT',tmpfile.name,SPLITTING_ENCODING_LP], stderr=subprocess.PIPE, stdout=subprocess.PIPE)
    out = iclingo.stdout.readline()
    while out[:-1] != '':
      if out[:6] == 'Answer':
	answerset = iclingo.stdout.readline()
	#output.write(answerset)
      out = iclingo.stdout.readline()
    #iclingo = None

    #output = sys.stdout
    #output.write(answerset)
    clause_name = old_clause_name
    processAnswerSet(answerset)
    
  elif root.tag == 'predicate':
    lit = parsePredicateXML(root)
    output.write('clause2pred(%s,%s).\n' %(clause_name,lit))
    
  elif root.tag == 'disjunction':
    for e in root.findall('*'):
      parseFormulaXML(e)
      
  elif root.tag == 'negation':
    global inNegationContext
    inNegationContext = True
    for e in root.findall('*'):
      parseFormulaXML(e)
      
  elif root.tag == 'tstp-logic-formula':
    tstp_formula = root.text
  
def parsePredicateXML(root):
  # root is the root node for predicate
  variables = set()
  global inNegationContext
  
  if not root:
    # propositional atom
    literal = root.get('name')
    if inNegationContext:
      literal = '_neg(' + literal + ')'
      inNegationContext = False
    return literal
  else:
    if root.get('name') == '=':
      literal = '_eq('
    else:
      literal = root.get('name')+'('
  
  argplace = 0
  for elem in root.findall('*'):
    argplace += 1
    if elem.tag == 'variable':
      var = '_var'+elem.get('name')
      variables.add(var)
      literal += var + ','
    else:
      #term (in function)
      literal += parseTermXML(elem,variables)+','
    if root.get('name') == '=' and argplace==1:
        literal += '_comma_,'
  
  literal = literal[:-1]+')'
  if inNegationContext:
    literal = '_neg(' + literal + ')'
    inNegationContext = False
  
  if len(variables) != 0:
    output.write('pred2var(%s,%s).\n' %(literal, reduce(lambda x,y: x+';'+y, variables)))
  #for v in variables:
    #output.write('pred2var(%s,%s).\n' %(literal,v))
    
  return literal

def parseTermXML(root, variables):
  # root is the root node for function (which can be constant or (deep)function)
  
  if not root:
    # above checks whether root has children or not
    #constant
    term = root.get('name')
    return term
  else:
    term = root.get('name')+'('
  
  for  elem in root.findall('*'):
    if elem.tag == 'variable':
      var = '_var'+elem.get('name')
      variables.add(var)
      term += var+','
    else:
      #function term (constant or functional)
      term += parseTermXML(elem,variables)+','
      
  term = term[:-1]+')'
  return term


def main():
  global options
  global output
  
  parser = OptionParser()
  parser.add_option("--iclingo-bin", dest="iclingo_bin", type="string", action="store",
    default='iclingo-banane', metavar='iclingo-bin-path',
    help='set the path for iClingo executable. Default assumes that the executable is in your path (Default: iclingo-banane)')
  
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
  
  global ICLINGO_BIN
  ICLINGO_BIN = options.iclingo_bin
  
  # output for all of the clauses to stdout
  for elem in root.findall('formula'):
    #output = sys.stdout
    parseFormulaXML(elem)
    
  #for elem in root.findall('formula'):
    ##clingo = subprocess.Popen(['clingo-banane','splitorder3.lp','-'], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    #clingo = subprocess.Popen(['iclingo-banane','--istop=UNSAT','-','splitinc.lp'], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    #output = clingo.stdin
    #parseFormulaXML(elem)
    #sys.stdout.write('=====\n')
    #sys.stdout.write(clingo.communicate()[0])
  

if __name__ == "__main__":
  main()