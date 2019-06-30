#! /usr/bin/env python   
# -*- coding: utf-8 -*-

#
# Transform script for FIMO
#
# Orkunt Sabuncu
#

import sys
import re
from optparse import OptionParser
from optparse import OptionValueError
import xml.etree.cElementTree as ElementTree
#import tempfile
import socket
import os
import gzip
import subprocess
import shlex
import cStringIO
from UnionFind import UnionFind
from itertools import groupby
import signal

INCVAR = '__inc'
VALVAR = 'Val_'

#VAR_PTRN = re.compile('[\(,]X(\d+)')
VAR_PTRN = re.compile('[\(,= ]X(\d+)')
TODICT_PTRN = re.compile('([\(,])X\d+')
VARPLACE_PTRN = re.compile('([\(,])_')

ONEVAR_PTRN = re.compile('X(\d+)')
FUNCNAME_PTRN = re.compile('([^\(]+)\(')

input = None
output = sys.stdout
options = None
inNegationContext = False
isEquality = False
isNonFlatPred = False
shouldOutputComma = False
occurs_list = []
occursterm_list = []
prepro_file = None
ICLINGO_BIN = 'iclingo-banane'
OLD_ICLINGO_BIN = 'iclingo-3.0.2'
iclingo_main_process = None

SATUNSAT_PTRN = re.compile('(SATISFIABLE|UNSATISFIABLE)')

functional_terms = dict()
constants = dict()
predicates = dict()
neg_predicates = dict()
pos_nonflat_predicates = dict()
base_functions = set()
base_predicates = set()
base_neg_predicates = set()
base_pos_predicates = set()
propositional_predicates = set()
subsumed_terms = set()

sorts_of_clause = dict()
sorts_of_disj = dict()

existential_variable = ''
inQuantifier = False
conj_main_lits = [] # list of (literal,andname,force_and_clause,lit_place_inquantifier) tuples
conj_aggregate = []
possible_conj_clause_body = None
and_clause = None
curr_clause_name = ''
isDeskolemizedInput = False
isDeskolemizedClause = False
lit_place_inquantifier = 0
isInDisjInQuantifier = False

has_conjecture = False

def parseFormulaXML(root,name2var):
  #print root.tag
  global inQuantifier  
  global shouldOutputComma
  global possible_conj_clause_body
  global and_clause
  global output
  global existential_variable
  global conj_main_lits
  global conj_aggregate
  global curr_clause_name
  #global has_conjecture
  global isDeskolemizedInput
  global isDeskolemizedClause
  global lit_place_inquantifier
  global isInDisjInQuantifier
  
  if root.tag == 'formula':
    # check formula is a clause
    if root.get('syntax') != 'clause':
      raise Exception('Expecting CNF input.')
    
    #if root.get('status') == 'negated_conjecture':
      #has_conjecture = True
    
    curr_clause_name = root.get('name')
    if root.find('.//variable') is None: 
    # with ElementTree v1.3 one can use: and root.find(".//predicate[@name]") is None:
      isPropositional = True
      for e in root.findall('.//predicate'):
	if e.get('name') == '=':
	  isPropositional = False
	  break
    else:
      isPropositional = False
      
    # check if the clause is a deskolemized one
    exi = root.find('.//quantifier')
    if exi is not None and exi.get('type')=='existential':
      isDeskolemizedClause = True
      isDeskolemizedInput = True
    else:
      isDeskolemizedClause = False
    
    global occurs_list
    global occursterm_list
    global sorts_of_clause
    global sorts_of_disj
    occurs_list = []
    occursterm_list = []
    sorts_of_clause = dict()
    sorts_of_disj = dict()
    outputFormulaPre(root.get('name'),isPropositional,isDeskolemizedClause)
    
    for e in root.findall('*'):
      parseFormulaXML(e,name2var)
      
    if isDeskolemizedClause:
      del name2var[existential_variable]
        
    outputFormulaPost(isPropositional,name2var,root.get('name'))
    if isDeskolemizedClause and and_clause.getvalue() != '':
      output.write('%s' %(and_clause.getvalue()))
    output.write('\n')
        
  elif root.tag == 'predicate':
    global isNonFlatPred
    global isEquality
    isNonFlatPred = False
    if inQuantifier:
      lit = parseConjPredicateXML(root,name2var)
      #print '\nDEBUG', lit, 'parsed in conj', 'isInDisjInQuantifier', isInDisjInQuantifier
      #print 'DEBUG', 'possible_conj_clause_body', possible_conj_clause_body.getvalue()
      #print 'DEBUG', 'and_clause', and_clause.getvalue()
    else:
      lit = parsePredicateXML(root,name2var)
      if not isEquality:
	findSortsFromElement(lit,sorts_of_clause,'pred')
      outputLiteral(lit)
    
  elif root.tag == 'disjunction':
    for e in root.findall('*'):
      if inQuantifier:
        if not isInDisjInQuantifier:
          if shouldOutputComma:
            output.write(', ')
          output.write('1 {')
          shouldOutputComma = False
        isInDisjInQuantifier = True
      parseFormulaXML(e,name2var)
    if isInDisjInQuantifier:
      output.write('}')
    isInDisjInQuantifier = False
  
  elif root.tag == 'negation':
    global inNegationContext
    inNegationContext = True
    for e in root.findall('*'):
      parseFormulaXML(e,name2var)
  
  elif root.tag == 'quantifier':
    #global shouldOutputComma
    #global possible_conj_clause_body
    #global and_clause
    #global output
    #global existential_variable
    #global conj_main_lits
    #global conj_aggregate
    shouldOutputComma_old = shouldOutputComma
    output_old = output
    shouldOutputComma = False
    inQuantifier = True
    possible_conj_clause_body = cStringIO.StringIO()
    and_clause = cStringIO.StringIO()
    output = possible_conj_clause_body
    existential_variable = ''
    conj_main_lits = []
    conj_aggregate = []
    lit_place_inquantifier = 1
    
    for e in root.findall('*'):
      if e.tag == 'variable':
        if e.get('name') not in name2var:
          name2var[e.get('name')] = len(name2var)+1
        existential_variable = e.get('name')
      else:
        parseFormulaXML(e,name2var)
    
    shouldOutputComma = shouldOutputComma_old
    output = output_old
    # decide whether an and clause is needed
    if len(conj_main_lits)==1 and not conj_main_lits[0][2]: # one main literal and it doesnt force and clause like eq
      andClauseNeeded = False
    else:
      andClauseNeeded = True
    outputConjAggregate(curr_clause_name,andClauseNeeded,'X'+str(name2var[existential_variable]))
    
    inQuantifier = False
    #print possible_conj_clause_body.getvalue()
    possible_conj_clause_body.close()
    
        
  elif root.tag == 'conjunction':
    # there are two child notes, for the second one increment the lit_place_inquantifier
    i = 0
    for e in root.findall('*'):
      i += 1
      if i== 2:
        lit_place_inquantifier += 1
      parseFormulaXML(e,name2var)
        

def outputAllClausesPre():
  output.write('\n%% clauses\n#cumulative %s.\n\n' %(INCVAR))
  
def outputAllFunctionsPre():
  output.write('\n%% functions\n#cumulative %s.\n\n' %(INCVAR))
  if options.nonflat_function_choices:
    output.write('% consistency checks for function interpretations\n')
    for (functor,arity) in base_functions:
      # check first whether interpretations for all base forms are  generated
      check = reduce(lambda x,y: x+','+y, ['_' for i in range(1,arity+1)])
      insertToDict('%s(%s)'%(functor,check), range(1,arity+1), functional_terms, True, '')
      
      terms1 = reduce(lambda x,y: x+','+y, ['T'+str(i) for i in range(1,arity+1)])
      terms2 = reduce(lambda x,y: x+','+y, ['V'+str(i) for i in range(1,arity+1)])
      if options.pure_preprocessing:
	output.write(':- not closed_subsumed_term(%s,%s), assign(%s(%s),V), ' %(functor,arity,functor,terms1))
      else:
	output.write(':- assign(%s(%s),V), ' %(functor,terms1))
      if options.dom_in_consistency:
	cardatoms = reduce(lambda x,y: x+','+y, ['not dom(T'+str(i)+')' for i in range(1,arity+1)])
	output.write('1{%s}, '%(cardatoms))
      for i in range(1,arity+1):
	output.write('assign(T%d,V%d), '%(i,i))
      output.write('not assign(%s(%s),V).\n' %(functor,terms2))
    output.write('\n')
  else:
    output.write('% interpretations of non-flat functions\n')
    for (functor,arity) in base_functions:
      # check first whether interpretations for all base forms are  generated
      check = reduce(lambda x,y: x+','+y, ['_' for i in range(1,arity+1)])
      insertToDict('%s(%s)'%(functor,check), range(1,arity+1), functional_terms, True, '')
      
      terms1 = reduce(lambda x,y: x+','+y, ['T'+str(i) for i in range(1,arity+1)])
      terms2 = reduce(lambda x,y: x+','+y, ['V'+str(i) for i in range(1,arity+1)])
      output.write('assigned(%s(%s),V,%s) :- func(%s(%s),nonflat), ' %(functor,terms1,INCVAR,functor,terms1))
      if options.pure_preprocessing:
	output.write('not closed_subsumed_term(%s,%s), ' %(functor,arity))
      if options.dom_in_consistency:
	cardatoms = reduce(lambda x,y: x+','+y, ['not dom(T'+str(i)+')' for i in range(1,arity+1)])
	output.write('1{%s}, '%(cardatoms))
      for i in range(1,arity+1):
	output.write('assigned(T%d,V%d,%s), '%(i,i,INCVAR))
      output.write('assigned(%s(%s),V,%s), not assigned(%s(%s),V,%s-1).\n' %(functor,terms2,INCVAR,functor,terms1,INCVAR))
    output.write('\n')
    
def outputAllConstantsPre():
  output.write('\n% constants\n#base.\n\n')
  
def outputAllPredicatesPre():
  output.write('\n%% literals\n#cumulative %s.\n\n' %(INCVAR))
  output.write('% consistency checks for predicate interpretations\n')
  
  # first be sure that all base forms are used ( if not add them)
  for (pred,arity) in base_predicates:
    # check first whether interpretations for all base forms are  generated
    check = reduce(lambda x,y: x+','+y, ['_' for i in range(1,arity+1)])
    insertToDict('%s(%s)'%(pred,check), range(1,arity+1), predicates, True, '')
  
  # consistency check for positive non-flat literals
  for (pred,arity) in base_pos_predicates:
    terms1 = reduce(lambda x,y: x+','+y, ['T'+str(i) for i in range(1,arity+1)])
    terms2 = reduce(lambda x,y: x+','+y, ['V'+str(i) for i in range(1,arity+1)])
    if options.pure_preprocessing:
      output.write(':- not closed_purepred(%s,%d), ' %(pred,arity))
    else:
      output.write(':- ')
    if options.use_pred_h:
      output.write('h(%s(%s)), ' %(pred,terms1))
    else:
      output.write('%s(%s), ' %(pred,terms1))
    if options.dom_in_consistency:
      cardatoms = reduce(lambda x,y: x+','+y, ['not dom(T'+str(i)+')' for i in range(1,arity+1)])
      output.write('1{%s}, '%(cardatoms))
    if options.use_not_assign:
      if options.nonflat_function_choices:
	for i in range(1,arity+1):
	  output.write('{not assign(T%d,V%d)}0, dom(V%d), '%(i,i,i))
      else:
	for i in range(1,arity+1):
	  output.write('{not assigned(T%d,V%d,%s)}0, dom(V%d), '%(i,i,INCVAR,i))
    else:
      if options.nonflat_function_choices:
	for i in range(1,arity+1):
	  output.write('assign(T%d,V%d), '%(i,i))
      else:
	for i in range(1,arity+1):
	  output.write('assigned(T%d,V%d,%s), '%(i,i,INCVAR))
    if options.use_pred_h:
      output.write('not h(%s(%s)).\n' %(pred,terms2))
    else:
      output.write('not %s(%s).\n' %(pred,terms2))
      
  # consistency check for negative non-flat literals
  for (pred,arity) in base_neg_predicates:
    terms1 = reduce(lambda x,y: x+','+y, ['T'+str(i) for i in range(1,arity+1)])
    terms2 = reduce(lambda x,y: x+','+y, ['V'+str(i) for i in range(1,arity+1)])
    if options.pure_preprocessing:
      output.write(':- not closed_purepred(%s,%d), ' %(pred,arity))
    else:
      output.write(':- ')
    if options.use_pred_h:
      output.write('not h(%s(%s)), pred(%s(%s)), ' %(pred,terms1,pred,terms1))
    else:
      output.write('negpred(%s(%s)), not %s(%s), ' %(pred,terms1,pred,terms1))
    if options.dom_in_consistency:
      cardatoms = reduce(lambda x,y: x+','+y, ['not dom(T'+str(i)+')' for i in range(1,arity+1)])
      output.write('1{%s}, '%(cardatoms))
    if options.use_not_assign:
      if options.nonflat_function_choices:
	for i in range(1,arity+1):
	  output.write('{not assign(T%d,V%d)}0, dom(V%d), '%(i,i,i))
      else:
	for i in range(1,arity+1):
	  output.write('{not assigned(T%d,V%d,%s)}0, dom(V%d), '%(i,i,INCVAR,i))
    else:
      if options.nonflat_function_choices:
	for i in range(1,arity+1):
	  output.write('assign(T%d,V%d), '%(i,i))
      else:
	for i in range(1,arity+1):
	  output.write('assigned(T%d,V%d,%s), '%(i,i,INCVAR))
    if options.use_pred_h:
      output.write('h(%s(%s)).\n' %(pred,terms2))
    else:
      output.write('%s(%s).\n' %(pred,terms2))
  
  
  #for (pred,arity) in base_predicates:
    ## check first whether interpretations for all base forms are  generated
    #check = reduce(lambda x,y: x+','+y, ['_' for i in range(1,arity+1)])
    #insertToDict('%s(%s)'%(pred,check), range(1,arity+1), predicates)
    ##if '%s(%s)'%(pred,check) not in predicates:
      ##outputPredicate('%s(%s)'%(pred,reduce(lambda x,y: x+','+y, ['X'+str(i) for i in range(1,arity+1)])), range(1,arity+1))
    #terms1 = reduce(lambda x,y: x+','+y, ['T'+str(i) for i in range(1,arity+1)])
    #terms2 = reduce(lambda x,y: x+','+y, ['V'+str(i) for i in range(1,arity+1)])
    #if options.use_pred_h:
      #output.write(':- h(%s(%s)), ' %(pred,terms1))
    #else:
      #output.write(':- %s(%s), ' %(pred,terms1))
    #if options.dom_in_consistency:
      #cardatoms = reduce(lambda x,y: x+','+y, ['not dom(T'+str(i)+')' for i in range(1,arity+1)])
      #output.write('1{%s}, '%(cardatoms))
    #for i in range(1,arity+1):
      #output.write('assign(T%d,V%d), '%(i,i))
    #if options.use_pred_h:
      #output.write('not h(%s(%s)).\n' %(pred,terms2))
    #else:
      #output.write('not %s(%s).\n' %(pred,terms2))
    
    #if options.consistency_check_negpred:
      #if (pred,arity) in base_neg_predicates:
	#if options.use_pred_h:
	  #output.write(':- not h(%s(%s)), pred(%s(%s)), ' %(pred,terms1,pred,terms1))
	#else:
	  #pass
	#if options.dom_in_consistency:
	  #cardatoms = reduce(lambda x,y: x+','+y, ['not dom(T'+str(i)+')' for i in range(1,arity+1)])
	  #output.write('1{%s}, '%(cardatoms))
	#for i in range(1,arity+1):
	  #output.write('assign(T%d,V%d), '%(i,i))
	#if options.use_pred_h:
	  #output.write('h(%s(%s)).\n' %(pred,terms2))
	#else:
	  #pass
      
  output.write('\n')

def outputAllPredicatesPreSpecific():
  output.write('\n%% literals\n#cumulative %s.\n\n' %(INCVAR))
  output.write('% consistency checks for predicate interpretations\n')
  
  # be sure that all base forms are used ( if not add them)
  for (pred,arity) in base_predicates:
    # check first whether interpretations for all base forms are  generated
    check = reduce(lambda x,y: x+','+y, ['_' for i in range(1,arity+1)])
    insertToDict('%s(%s)'%(pred,check), range(1,arity+1), predicates, True, '')
  
  # consistency check for positive non-flat literals
  for (l,varlist) in pos_nonflat_predicates.iteritems():
    if options.pure_preprocessing:
      occlist = findOccurrencesInDictString(l)
    lit = VARPLACE_PTRN.sub(r'\1%s',l)
    pred = lit[:lit.find('(')]
    for vars in varlist:
      lit1 = lit % tuple(['X'+str(i) for i in vars])
      args = findArguments(lit1)
      arity = len(args)
      
      if options.pure_preprocessing:
	prepro_part = 'not closed_purepred(%s,%d)' %(occlist[len(occlist)-1])
	prepro_part += ', ' + reduce(lambda x,y: x+', '+y, ['not closed_subsumed_term('+f+','+str(a)+')' for (f,a) in occlist[:-1]])
	output.write(':- %s, ' %(prepro_part))
      else:
	output.write(':- ')
      if options.use_pred_h:
	output.write('h(%s), ' %(lit1))
      else:
	output.write('%s, ' %(lit1))
      #no need to check dom_in_consistency now since we already know that it's not flat
      if options.use_not_assign:
	for i in range(1,arity+1):
	  if options.nonflat_function_choices or (not options.assigned_only and len(findOccurrencesInDictString(TODICT_PTRN.sub(r'\1_',args[i-1]))) == 1):
	    output.write('{not assign(%s,V%d)}0, dom(V%d), '%(args[i-1],i,i))
	  else:
	    output.write('{not assigned(%s,V%d,%s)}0, dom(V%d), '%(args[i-1],i,INCVAR,i))
      else:
	for i in range(1,arity+1):
	  if options.nonflat_function_choices or (not options.assigned_only and len(findOccurrencesInDictString(TODICT_PTRN.sub(r'\1_',args[i-1]))) == 1):
	    output.write('assign(%s,V%d), '%(args[i-1],i))
	  else:
	    output.write('assigned(%s,V%d,%s), '%(args[i-1],i,INCVAR))
      terms2 = reduce(lambda x,y: x+','+y, ['V'+str(i) for i in range(1,arity+1)])
      if options.use_pred_h:
	output.write('not h(%s(%s)).\n' %(pred,terms2))
      else:
	output.write('not %s(%s).\n' %(pred,terms2))
      
  # consistency check for negative non-flat literals
  for (l,varlist) in neg_predicates.iteritems():
    if options.pure_preprocessing:
      occlist = findOccurrencesInDictString(l)
    lit = VARPLACE_PTRN.sub(r'\1%s',l)
    pred = lit[:lit.find('(')]
    for (vars,cla) in varlist:
      lit1 = lit % tuple(['X'+str(i) for i in vars])
      args = findArguments(lit1)
      arity = len(args)
      
      if options.pure_preprocessing:
	prepro_part = 'not closed_purepred(%s,%d)' %(occlist[len(occlist)-1])
	prepro_part += ', ' + reduce(lambda x,y: x+', '+y, ['not closed_subsumed_term('+f+','+str(a)+')' for (f,a) in occlist[:-1]])
	output.write(':- %s, ' %(prepro_part))
      else:
	output.write(':- ')
      if options.use_pred_h:
	output.write('not h(%s), pred(%s), ' %(lit1,lit1))
      else:
	output.write('negpred(%s), not %s, ' %(lit1,lit1))
      #no need to check dom_in_consistency now since we already know that it's not flat
      if options.use_not_assign:
	for i in range(1,arity+1):
	  if options.nonflat_function_choices or (not options.assigned_only and len(findOccurrencesInDictString(TODICT_PTRN.sub(r'\1_',args[i-1]))) == 1):
	    output.write('{not assign(%s,V%d)}0, dom(V%d), '%(args[i-1],i,i))
	  else:
	    output.write('{not assigned(%s,V%d,%s)}0, dom(V%d), '%(args[i-1],i,INCVAR,i))
      else:
	for i in range(1,arity+1):
	  if options.nonflat_function_choices or (not options.assigned_only and len(findOccurrencesInDictString(TODICT_PTRN.sub(r'\1_',args[i-1]))) == 1):
	    output.write('assign(%s,V%d), '%(args[i-1],i))
	  else:
	    output.write('assigned(%s,V%d,%s), '%(args[i-1],i,INCVAR))
      terms2 = reduce(lambda x,y: x+','+y, ['V'+str(i) for i in range(1,arity+1)])
      if options.use_pred_h:
	output.write('h(%s(%s)).\n' %(pred,terms2))
      else:
	output.write('%s(%s).\n' %(pred,terms2))
      
  output.write('\n')

def outputOccursAsComment():
  output.write('\n%% positive occurrances debug\n')
  
  for (l,varlist) in predicates.iteritems():
    output.write('%% %s %s\n' %(l,str(varlist)))
  
  output.write('\n%% negative occurrances debug\n')
  
  for (l,varlist) in neg_predicates.iteritems():
    output.write('%% %s %s\n' %(l,str(varlist)))
  
  output.write('\n%% function occurrances debug\n')
  
  for (l,varlist) in functional_terms.iteritems():
    output.write('%% %s %s\n' %(l,str(varlist)))
    
def outputIndependentPart():
  template1 = '''
#cumulative %s.

dom(%s).
assign(%s,%s).

'''
  output.write(template1 %(INCVAR,INCVAR,INCVAR,INCVAR))
  
  if options.sort_inference:
    output.write('sort_element(S,D) :- dom(D), sort_max(S,M), D<=M.\n\n')
  
  if options.symbreak:
    output.write('%% with symmetry break\n{ assign(T,%s) } :- cons(T), _order(T,O), %s<=O.\n\n' %(INCVAR,INCVAR))
  else:
    output.write('%% without symmetry break\n{ assign(T,%s) } :- cons(T).\n\n' %(INCVAR))
    
  if options.canonical_form == 'Normal':
    if not options.sort_inference:
      output.write('''
%% force canonical form with normal rules
cano_assigned(C,%s) :- assign(C,%s), _order(C,N).
cano_assigned(C,%s) :- cano_assigned(D,%s), _order(D,N-1), _order(C,N).
:- assign(C,%s), not cano_assigned(D,%s-1), _order(D,N-1), _order(C,N), dom(%s;%s-1).
''' %(INCVAR,INCVAR,INCVAR,INCVAR,INCVAR,INCVAR,INCVAR,INCVAR))
    else:
      output.write('''
%% force canonical form with normal rules
cano_assigned(C,%s) :- assign(C,%s), _order(C,N).
cano_assigned(C,%s) :- cano_assigned(D,%s), _order(D,N-1), _order(C,N), in_sort(slot(f(D,0),1),S), in_sort(slot(f(C,0),1),S).
:- assign(C,%s), not cano_assigned(D,%s-1), _order(D,N-1), _order(C,N), in_sort(slot(f(D,0),1),S), in_sort(slot(f(C,0),1),S), dom(%s;%s-1).
''' %(INCVAR,INCVAR,INCVAR,INCVAR,INCVAR,INCVAR,INCVAR,INCVAR))
  elif options.canonical_form == 'NormalInPaper':
    if not options.sort_inference:
      output.write('''
%% force canonical form with normal rules (one constraint for each constant)
cano_assigned(C,%s) :- assign(C,%s), _order(C,N).
cano_assigned(C,%s) :- cano_assigned(D,%s), _order(D,N-1), _order(C,N).
:- cons(T), assign(T,%s), not cano_assigned(T,%s-1), 1 < %s.
''' %(INCVAR,INCVAR,INCVAR,INCVAR,INCVAR,INCVAR,INCVAR))
    else:
      output.write('''
%% force canonical form with normal rules (one constraint for each constant)
cano_assigned(C,%s) :- assign(C,%s), _order(C,N).
cano_assigned(C,%s) :- cano_assigned(D,%s), _order(D,N-1), _order(C,N), in_sort(slot(f(D,0),1),S), in_sort(slot(f(C,0),1),S).
:- cons(T), assign(T,%s), not cano_assigned(T,%s-1), 1 < %s.
''' %(INCVAR,INCVAR,INCVAR,INCVAR,INCVAR,INCVAR,INCVAR))
  elif options.canonical_form == 'Fat':
    if not options.sort_inference:
      output.write('''
%% force canonical form with cardinality literal
:- assign(D,%s), _order(D,O1), { assign(D2,%s-1):_order(D2,O2):O2<O1 } 0 , dom(%s;%s-1).
''' %(INCVAR,INCVAR,INCVAR,INCVAR))
    else:
      output.write('''
%% force canonical form with cardinality literal
:- assign(D,%s), _order(D,O1), in_sort(slot(f(D,0),1),S), { assign(D2,%s-1):in_sort(slot(f(D2,0),1),S):_order(D2,O2):O2<O1 } 0 , dom(%s;%s-1).
''' %(INCVAR,INCVAR,INCVAR,INCVAR))

  template2 = '''
:- assign(T,V1), assign(T,V2), V1<V2.

'''
  output.write(template2)
  
  if options.nonflat_function_choices:
    output.write('{ assign(T,V) } :- func(T,F), dom(V).\n')
  else:
    template2_detnonflat  = '''
{ assign(T,V) } :- func(T,flat), dom(V).

assigned(%s,%s,%s).
assigned(T,V,%s) :- assign(T,V), not assigned(T,V,%s-1).
assigned(T,V,%s) :- assigned(T,V,%s-1).
'''
    output.write(template2_detnonflat % (INCVAR,INCVAR,INCVAR,INCVAR,INCVAR,INCVAR,INCVAR))

  if options.use_pred_h:
     output.write('{ h(P) } :- pred(P), not interpreted(P).\n')

  if options.pure_preprocessing:
    pure_template = '''
    
#base.
predicate(P,A) :- occurs(P,A,Pol,C).
subsumed(C) :- pure(P,A,Pol), occurs(P,A,Pol,C).
subsumed(C) :- subsumed(_deskol(C,P1)):P1=1..P, clause_part(C,P).
subsumed(_deskol(C,P1)) :- subsumed(C), P1=1..P, clause_part(C,P).
pure(P,A,pos) :- predicate(P,A), subsumed(C):occurs(P,A,neg,C), not pure(P,A,neg).
pure(P,A,neg) :- predicate(P,A), subsumed(C):occurs(P,A,pos,C), not pure(P,A,pos).
'''
    output.write(pure_template)
    output.write('%% preprocessing logic program : %s\n' %(prepro_file.name))
    prepro_file.write(pure_template)
    # only to preprocessing logic program
    pure_template2 = '''
purepred(P,A) :- pure(P,A,Pol).
term(F,A) :- occurs_term(F,A,C).    
subsumed_term(F,A) :- term(F,A), subsumed(C):occurs_term(F,A,C).
'''
    prepro_file.write(pure_template2)

  if options.sort_inference:
    sort_template2 = '''
sort_name(S) :- in_sort(Sl,S).

sort_has_func(S) :- in_sort(slot(f(F,A),A+1),S), A!=0.

sort_has_eq(S,var2) :- in_sort(slot(C,eq(A1,A2,var2)),S).
sort_has_eq(S,var1) :- in_sort(slot(C,eq(A1,A2,var1)),S).
sort_has_eq(S,term2) :- in_sort(slot(C,eq(A1,A2,term2)),S).

sort_cons_count(S,M) :- M = #count{ in_sort(slot(f(F,0),1),S) }, sort_name(S).

sort_max(S,#supremum) :- sort_has_func(S).
sort_max(S,#supremum) :- sort_has_eq(S,var2).
%sort_max(S,M) :- sort_cons_count(S,M), not sort_has_func(S), not sort_has_eq(S,var2;var1;term2).
%sort_max(S,M+1) :- sort_cons_count(S,M), not sort_has_func(S), not sort_has_eq(S,var2), 1{ sort_has_eq(S,var1;term2) }.
sort_max(S,M) :- sort_cons_count(S,M), M!=0, not sort_has_func(S), not sort_has_eq(S,var2;var1;term2).
sort_max(S,M+1) :- sort_cons_count(S,M), M!=0, not sort_has_func(S), not sort_has_eq(S,var2), 1{ sort_has_eq(S,var1;term2) }.
sort_max(S,1) :- sort_cons_count(S,0), not sort_has_func(S), not sort_has_eq(S,var2;var1;term2).
sort_max(S,1) :- sort_cons_count(S,0), not sort_has_func(S), not sort_has_eq(S,var2), 1{ sort_has_eq(S,var1;term2) }.    
'''
    if not options.asp_based_sorts:
      output.write('%% preprocessing logic program : %s\n' %(prepro_file.name))
      prepro_file.write('sort_slot(S) :- sort_occurs(C,S,V).\n')
      prepro_file.write('same_value(S1,S2) :- sort_occurs(C,S1,V), sort_occurs(C,S2,V), S1<S2.\n')
      output.write('#base.\n')
      output.write(sort_template2)
    else:  
      sort_template1 = '''
sort_slot(S) :- sort_occurs(C,S,V).

same_value(S1,S2) :- sort_occurs(C,S1,V), sort_occurs(C,S2,V), S1<S2.
same_value(S1,S2) :- same_value(S1,SX), same_value(SX,S2), S1<S2.
same_value(S1,S2) :- same_value(S1,SX), same_value(S2,SX), S1<S2.

sort_repr(S) :- sort_slot(S), not same_value(SX,S):sort_slot(SX).

in_sort(S,1) :- sort_repr(S), not sort_repr(SX):sort_repr(SX):SX<S.
in_sort(S,X+1) :- sort_repr(S;SP), in_sort(SP,X), SP<S, not sort_repr(SM):sort_repr(SM):SM<S:SM>SP.
in_sort(S,X) :- sort_repr(SR), sort_slot(S), in_sort(SR,X), same_value(SR,S).
'''
      output.write('%% preprocessing logic program : %s\n' %(prepro_file.name))
      prepro_file.write(sort_template1)
      prepro_file.write(sort_template2)

  if options.dummy_assign :
    output.write('\nassigned(dummy,1..N,dummy) :- N = #count { func(T,F), cons(C) }.\n')
    output.write('assign(-1*N..-1,dummy) :- N = #count { func(T,F), cons(C) }.\n')
    
  template3 = '''

#volatile %s.

:- cons(T), { assign(T,D): dom(D) } 0.
'''  
  output.write(template3 %(INCVAR))
  if options.nonflat_function_choices:
    output.write(':- func(T,F), { assign(T,D): dom(D) } 0.\n')
  else:
    output.write(':- func(T,flat), { assign(T,D): dom(D) } 0.\n:- func(T,nonflat), { assigned(T,D,%s): dom(D) } 0.\n' %(INCVAR))
  
  template4  = '''

#hide.
#show dom/1.
#show assign/2.
'''
  output.write(template4)
      
  if options.pure_preprocessing:
    output.write('#show pure/3.\n#show subsumed/1.\n')
  
  if options.use_pred_h:
    output.write('#show h/1.\n')
  else:
    for (pred,arity) in base_predicates:
      output.write('#show %s/%d.\n' %(pred,arity))
    for pred in propositional_predicates:
      output.write('#show %s.\n' %(pred))
      
  # EPR related part
  output.write('\n#cumulative %s.\n' %(INCVAR))
  output.write(':- is_epr, epr_upperbound(M), %s>M.\n' %(INCVAR))
  if options.sort_inference:
    template_epr = '''
#base.
is_epr :- not sort_has_func(S):sort_name(S).
epr_upperbound(M) :- M = #max [ sort_cons_count(S,C):sort_name(S) = C ], M!=0, M!=#infimum, is_epr.
epr_upperbound(1) :- M = #max [ sort_cons_count(S,C):sort_name(S) = C ], M==0, is_epr.
epr_upperbound(1) :- M = #max [ sort_cons_count(S,C):sort_name(S) = C ], M==#infimum, is_epr.
#show is_epr.
'''
    output.write(template_epr)
  else:
    template_epr = '''
#base.
epr_upperbound(M) :- M = #count {cons(C):not closed_subsumed_term(C,0)}, M!=0, is_epr.
epr_upperbound(1) :- M = #count {cons(C):not closed_subsumed_term(C,0)}, M==0, is_epr.
#show is_epr.
'''
    output.write(template_epr)
    global isDeskolemizedInput
    if len(base_functions) == 0 and not isDeskolemizedInput:
      output.write('is_epr.\n')

def outputPreprocessingResultsUnionFind():
  global prepro_file
  
  # call iclingo on the preprocessing logic program
  prepro_file.write('#hide.\n')
  if options.pure_preprocessing:
    prepro_file.write('#show purepred/2.\n#show subsumed/1.\n#show subsumed_term/2.\n')
  prepro_file.write('#show sort_slot/1.\n#show same_value/2.\n')
  prepro_file.write('turn(purepreprocessing) :- not cancel(purepreprocessing).\n')  
  prepro_file.write('turn(sortinference) :- not cancel(sortinference).\n')  
  prepro_file.write('turn(sortinference).\n')
  prepro_file.write('closed_subsumed(C) :- subsumed(C).\n')
  
  if not options.pure_preprocessing:
    prepro_file.write('cancel(purepreprocessing).\n')
    
  prepro_file.close()
  if options.gzip_temp_file:
    zcat_process = subprocess.Popen(['time','zcat',prepro_file.name], stderr=subprocess.PIPE, stdout=subprocess.PIPE)
    iclingo_process = subprocess.Popen([OLD_ICLINGO_BIN], stdin=zcat_process.stdout, stderr=subprocess.PIPE, stdout=subprocess.PIPE)
  else:
    iclingo_process = subprocess.Popen(['time',OLD_ICLINGO_BIN,prepro_file.name], stderr=subprocess.PIPE, stdout=subprocess.PIPE)
  # iclingo-3.0.3 and greater has a bug !!
  #iclingo_process = subprocess.Popen(['time',ICLINGO_BIN,prepro_file.name], stderr=subprocess.PIPE, stdout=subprocess.PIPE)
  out = iclingo_process.stdout.readline()
  while out[:6]!= 'Answer':
    out = iclingo_process.stdout.readline()
  # now we are ready to parse
  out = iclingo_process.stdout.readline().split()
  
  output.write('\n%% preprocessing results\n')
  output.write('#base.\n')
  if options.pure_preprocessing:
    for i in filter(lambda x: x.startswith('subsumed('), out):
      output.write('closed_%s.\n' %(i))
    for i in filter(lambda x: x.startswith('purepred('), out):
      output.write('closed_%s.\n' %(i))
    for i in filter(lambda x: x.startswith('subsumed_term('), out):
      output.write('closed_%s.\n' %(i))
      r = re.match('subsumed_term\((.+),(\d+)\)',i)
      subsumed_terms.add((r.group(1),int(r.group(2))))
  
  slots = []
  for i in filter(lambda x: x.startswith('sort_slot('), out):
    slots.append(i[i.find('(')+1:-1])
  
  # run union-find
  UF = UnionFind()
  UF.insert_objects(slots)
  for i in filter(lambda x: x.startswith('same_value('), out):
    args = findArguments(i)
    UF.union(args[0],args[1])
  
  # output sorts
  sorts2num = dict()
  for s in slots:
    sortname = UF.find(s)
    if sortname not in sorts2num:
      sorts2num[sortname] = len(sorts2num)+1
    output.write('in_sort(%s,%d).\n' %(s,sorts2num[sortname]))
      
  for l in iclingo_process.stderr.readlines():
    output.write('%% %s' %(l))
  output.write('\n')

def outputPreprocessingResults():
  global prepro_file
  
  if options.sort_inference and not options.asp_based_sorts:
    outputPreprocessingResultsUnionFind()
    return
  
  # call iclingo on the preprocessing logic program
  prepro_file.write('#hide.\n')
  if options.pure_preprocessing:
    prepro_file.write('#show purepred/2.\n#show subsumed/1.\n#show subsumed_term/2.\n')
  if options.sort_inference:
    prepro_file.write('#show in_sort/2.\n#show sort_name/1.\n#show sort_has_func/1.\n')
    prepro_file.write('#show sort_has_eq/2.\n#show sort_cons_count/2.\n#show sort_max/2.\n')
  prepro_file.write('turn(purepreprocessing) :- not cancel(purepreprocessing).\n')  
  prepro_file.write('turn(sortinference) :- not cancel(sortinference).\n')  
  
  # FIRST RUN PURE PREPROCESSING (if needed)
  if options.pure_preprocessing:
    prepro_file.write('cancel(sortinference).\n')
    prepro_file.close()
    if options.gzip_temp_file:
      zcat_process = subprocess.Popen(['time','zcat',prepro_file.name], stderr=subprocess.PIPE, stdout=subprocess.PIPE)
      iclingo_process = subprocess.Popen([ICLINGO_BIN], stdin=zcat_process.stdout, stderr=subprocess.PIPE, stdout=subprocess.PIPE)
    else:
      iclingo_process = subprocess.Popen(['time',ICLINGO_BIN,prepro_file.name], stderr=subprocess.PIPE, stdout=subprocess.PIPE)
    out = iclingo_process.stdout.readline()
    while out[:6]!= 'Answer':
      out = iclingo_process.stdout.readline()
    # now we are ready to parse
    out = iclingo_process.stdout.readline().split()
    #closed1 = filter(lambda x: x.startswith('subsumed'), out)
    #closed2 = filter(lambda x: x.startswith('purepred'), out)
    #closed3 = filter(lambda x: x.startswith('subsumed_term'), out)
    
    # FOR SECOND RUN REOPEN THE FILE
    if options.sort_inference:
      if options.gzip_temp_file:
        prepro_file = gzip(prepro_file.name,'a',3)
      else:
        prepro_file = open(prepro_file.name,'a')
      prepro_file.write('cancel(purepreprocessing).\n')
      prepro_file.write('turn(sortinference).\n')
    
    output.write('\n%% preprocessing results\n')
    output.write('#base.\n')
    if options.pure_preprocessing:
      for i in filter(lambda x: x.startswith('subsumed('), out):
        output.write('closed_%s.\n' %(i))
        if options.sort_inference:
          prepro_file.write('closed_%s.\n' %(i))
      for i in filter(lambda x: x.startswith('purepred('), out):
        output.write('closed_%s.\n' %(i))
      for i in filter(lambda x: x.startswith('subsumed_term('), out):
        output.write('closed_%s.\n' %(i))
        r = re.match('subsumed_term\((.+),(\d+)\)',i)
        subsumed_terms.add((r.group(1),int(r.group(2))))
        
    for l in iclingo_process.stderr.readlines():
      output.write('%% %s' %(l))
    output.write('\n')
    
  if not options.pure_preprocessing and options.sort_inference:
    prepro_file.write('cancel(purepreprocessing).\n')
  
  if options.sort_inference:
    prepro_file.close()
    if options.gzip_temp_file:
      zcat_process = subprocess.Popen(['time','zcat',prepro_file.name], stderr=subprocess.PIPE, stdout=subprocess.PIPE)
      iclingo_process = subprocess.Popen([ICLINGO_BIN], stdin=zcat_process.stdout, stderr=subprocess.PIPE, stdout=subprocess.PIPE)
    else:
      iclingo_process = subprocess.Popen(['time',ICLINGO_BIN,prepro_file.name], stderr=subprocess.PIPE, stdout=subprocess.PIPE)
    out = iclingo_process.stdout.readline()
    while out[:6]!= 'Answer':
      out = iclingo_process.stdout.readline()
    # now we are ready to parse
    out = iclingo_process.stdout.readline().split()
    
    for i in filter(lambda x: x.startswith('in_sort(') or x.startswith('sort_name(') or \
x.startswith('sort_has_func(') or x.startswith('sort_has_eq(') or \
x.startswith('sort_cons_count(') or x.startswith('sort_max('), out):
      output.write('%s.\n' %(i))
    
    for l in iclingo_process.stderr.readlines():
      output.write('%% %s' %(l))
    output.write('\n')
  
def outputAllConstants():
  order = 0
  for c in constants:
    if options.pure_preprocessing:
      if (c,0) in subsumed_terms:
        continue
    order += 1
    if options.sort_inference:
      output.write('cons(%s).\n_all_order(%s,%d).\n'%(c,c,order))
    else:
      output.write('cons(%s).\n_order(%s,%d).\n'%(c,c,order))
  if options.sort_inference:
    order_template='''
_order(C,M+1) :- _all_order(C,O), in_sort(slot(f(C,0),1),S), M=#count{ cons(C1):in_sort(slot(f(C1,0),1),S):_all_order(C1,O1):O1<O }.
'''
    output.write(order_template)
  
def outputFunction(term,vars,isflat):
  if isflat:
    flatstr = 'flat'
  else:
    flatstr = 'nonflat'
  if len(vars) == 0:
    output.write('#base.\nfunc(%s,%s).\n#cumulative %s.\n' %(term,flatstr,INCVAR))
  else:  
    varPool = reduce(lambda x,y: x+';'+y, ['X'+str(i) for i in set(vars)])
    if options.sort_inference:
      output.write('func(%s,%s) :- ' %(term,flatstr))
      sorts = dict()
      findSortsFromElement(term,sorts,'func')
      for (var,sortstr) in sorts.iteritems():
        output.write('%s, sort_element(S%d,X%d), ' %(sortstr,var,var))
      output.write('dom(%s).\n' %(varPool))
    else:
      output.write('func(%s,%s) :- dom(%s).\n' %(term,flatstr,varPool))
    
def outputFunctionWithPurePre(term,vars,isflat,occlist,sourceclausesstr):
  if isflat:
    flatstr = 'flat'
  else:
    flatstr = 'nonflat'
  prepro_part = reduce(lambda x,y: x+', '+y, ['not closed_subsumed_term('+f+','+str(a)+')' for (f,a) in occlist])
  if len(vars) == 0:
    if sourceclausesstr == '':
      output.write('#base.\nfunc(%s,%s) :- %s.\n#cumulative %s.\n' %(term,flatstr,prepro_part,INCVAR))
    else:
      output.write('#base.\nfunc(%s,%s) :- %s, %s.\n#cumulative %s.\n' %(term,flatstr,prepro_part,sourceclausesstr,INCVAR))
  else:  
    varPool = reduce(lambda x,y: x+';'+y, ['X'+str(i) for i in set(vars)])
    if options.sort_inference:
      output.write('func(%s,%s) :- %s, ' %(term,flatstr,prepro_part))
      sorts = dict()
      findSortsFromElement(term,sorts,'func')
      for (var,sortstr) in sorts.iteritems():
        output.write('%s, sort_element(S%d,X%d), ' %(sortstr,var,var))
      if sourceclausesstr != '':
	output.write('%s, '%(sourceclausesstr))
      output.write('dom(%s).\n' %(varPool))
    else:
      if sourceclausesstr == '':
	output.write('func(%s,%s) :- %s, dom(%s).\n' %(term,flatstr,prepro_part,varPool))
      else:
	output.write('func(%s,%s) :- %s, %s, dom(%s).\n' %(term,flatstr,prepro_part,sourceclausesstr,varPool))
  
def outputAllFunctions():
  for (t,varlist) in functional_terms.iteritems():
    occlist = findOccurrencesInDictString(t)
    if len(occlist)>1:
      isflat = False
    else:
      isflat = True
    term = VARPLACE_PTRN.sub(r'\1%s',t)
    for (vars,cla) in varlist:
      term1 = term % tuple(['X'+str(i) for i in vars])
      #varPool = reduce(lambda x,y: x+';'+y, ['X'+str(i) for i in set(vars)])
      if options.pure_preprocessing:
	sourceclausesstr = '' if len(cla)==0 or isflat else '1 { not closed_subsumed(%s) }' %(reduce(lambda x,y: x+';'+y, [i for i in cla]))
	outputFunctionWithPurePre(term1,vars,isflat,occlist,sourceclausesstr)
      else:
	outputFunction(term1,vars,isflat)

def outputPredicate(lit,vars):
  if len(vars) == 0:
    if options.use_pred_h:
      output.write('#base.\npred(%s).\n{ h(%s) }.\ninterpreted(%s).\n#cumulative %s.\n' %(lit,lit,lit,INCVAR))
      #output.write('#base.\npred(%s).\n#cumulative %s.\n' %(lit,INCVAR))
    else:
      output.write('#base.\n{ %s }.\n#cumulative %s.\n' %(lit,INCVAR))
  else:  
    varPool = reduce(lambda x,y: x+';'+y, ['X'+str(i) for i in set(vars)])
    if options.use_pred_h:
      if options.sort_inference:
        output.write('pred(%s) :- ' %(lit))
        sorts = dict()
        findSortsFromElement(lit,sorts,'pred')
        for (var,sortstr) in sorts.iteritems():
          output.write('%s, sort_element(S%d,X%d), ' %(sortstr,var,var))
        output.write('dom(%s).\n' %(varPool))
      else:
        output.write('pred(%s) :- dom(%s).\n' %(lit,varPool))
    else:
      if options.sort_inference:
        output.write('{ %s } :- ' %(lit))
        sorts = dict()
        findSortsFromElement(lit,sorts,'pred')
        for (var,sortstr) in sorts.iteritems():
          output.write('%s, sort_element(S%d,X%d), ' %(sortstr,var,var))
        output.write('dom(%s).\n' %(varPool))
      else:
        output.write('{ %s } :- dom(%s).\n' %(lit,varPool))

def outputNegPredicate(lit,vars):
  if len(vars) == 0:
    output.write('#base.\nnegpred(%s).\n#cumulative %s.\n' %(lit,INCVAR))
  else:  
    varPool = reduce(lambda x,y: x+';'+y, ['X'+str(i) for i in set(vars)])
    if options.sort_inference:
      output.write('negpred(%s) :- ' %(lit))
      sorts = dict()
      findSortsFromElement(lit,sorts,'pred')
      for (var,sortstr) in sorts.iteritems():
        output.write('%s, sort_element(S%d,X%d), ' %(sortstr,var,var))
      output.write('dom(%s).\n' %(varPool))
    else:
      output.write('negpred(%s) :- dom(%s).\n' %(lit,varPool))

def outputPredicateWithPurePre(lit,vars,occlist,sourceclausesstr):
  prepro_part = 'not closed_purepred(%s,%d)' %(occlist[len(occlist)-1])
  if len(occlist) != 1:
    prepro_part += ', ' + reduce(lambda x,y: x+', '+y, ['not closed_subsumed_term('+f+','+str(a)+')' for (f,a) in occlist[:-1]])
  if len(vars) == 0:
    if options.use_pred_h:
      if sourceclausesstr == '':
	output.write('#base.\npred(%s).\n{ h(%s) } :- %s.\ninterpreted(%s) :- %s.\n#cumulative %s.\n' %(lit,lit,prepro_part,lit,prepro_part,INCVAR))
      else:
	output.write('#base.\npred(%s) :- %s.\n{ h(%s) } :- %s, %s.\ninterpreted(%s) :- %s, %s.\n#cumulative %s.\n' %(lit,sourceclausesstr, lit,prepro_part,sourceclausesstr, lit,prepro_part,sourceclausesstr, INCVAR))
      #output.write('#base.\npred(%s).\n#cumulative %s.\n' %(lit,INCVAR))
    else:
      if sourceclausesstr == '':
	output.write('#base.\n{ %s } :- %s.\n#cumulative %s.\n' %(lit,prepro_part,INCVAR))
      else:
	output.write('#base.\n{ %s } :- %s, %s.\n#cumulative %s.\n' %(lit,prepro_part,sourceclausesstr, INCVAR))
  else:  
    varPool = reduce(lambda x,y: x+';'+y, ['X'+str(i) for i in set(vars)])
    if options.use_pred_h:
      if options.sort_inference:
        output.write('pred(%s) :- %s, ' %(lit,prepro_part))
        sorts = dict()
        findSortsFromElement(lit,sorts,'pred')
        for (var,sortstr) in sorts.iteritems():
          output.write('%s, sort_element(S%d,X%d), ' %(sortstr,var,var))
	if sourceclausesstr != '':
	  output.write('%s, '%(sourceclausesstr))
        output.write('dom(%s).\n' %(varPool))
      else:
	if sourceclausesstr == '':
	  output.write('pred(%s) :- %s, dom(%s).\n' %(lit,prepro_part,varPool))
	else:
	  output.write('pred(%s) :- %s, %s, dom(%s).\n' %(lit,prepro_part,sourceclausesstr,varPool))
    else:
      if options.sort_inference:
        output.write('{ %s } :- %s, ' %(lit,prepro_part))
        sorts = dict()
        findSortsFromElement(lit,sorts,'pred')
        for (var,sortstr) in sorts.iteritems():
          output.write('%s, sort_element(S%d,X%d), ' %(sortstr,var,var))
        if sourceclausesstr != '':
	  output.write('%s, '%(sourceclausesstr))
        output.write('dom(%s).\n' %(varPool))
      else:
	if sourceclausesstr == '':
	  output.write('{ %s } :- %s, dom(%s).\n' %(lit,prepro_part,varPool))
	else:
	  output.write('{ %s } :- %s, %s, dom(%s).\n' %(lit,prepro_part,sourceclausesstr,varPool))

def outputNegPredicateWithPurePre(lit,vars,occlist,sourceclausesstr):
  prepro_part = 'not closed_purepred(%s,%d)' %(occlist[len(occlist)-1])
  if len(occlist) != 1:
    prepro_part += ', '+reduce(lambda x,y: x+', '+y, ['not closed_subsumed_term('+f+','+str(a)+')' for (f,a) in occlist[:-1]])
  if len(vars) == 0:
    if sourceclausesstr == '':
      output.write('#base.\nnegpred(%s) :- %s.\n#cumulative %s.\n' %(lit,prepro_part,INCVAR))
    else:
      output.write('#base.\nnegpred(%s) :- %s, %s.\n#cumulative %s.\n' %(lit,prepro_part,sourceclausesstr,INCVAR))
  else:  
    varPool = reduce(lambda x,y: x+';'+y, ['X'+str(i) for i in set(vars)])
    if options.sort_inference:
      output.write('negpred(%s) :- %s, ' %(lit,prepro_part))
      sorts = dict()
      findSortsFromElement(lit,sorts,'pred')
      for (var,sortstr) in sorts.iteritems():
        output.write('%s, sort_element(S%d,X%d), ' %(sortstr,var,var))
      if sourceclausesstr != '':
	output.write('%s, '%(sourceclausesstr))
      output.write('dom(%s).\n' %(varPool))
    else:
      if sourceclausesstr == '':
	output.write('negpred(%s) :- %s, dom(%s).\n' %(lit,prepro_part,varPool))
      else:
	output.write('negpred(%s) :- %s, %s, dom(%s).\n' %(lit,prepro_part,sourceclausesstr,varPool))

def outputAllPredicates():
  for (l,varlist) in predicates.iteritems():
    if options.pure_preprocessing:
      occlist = findOccurrencesInDictString(l)
      if len(occlist)>1:
        isflat = False
      else:
        isflat = True
    lit = VARPLACE_PTRN.sub(r'\1%s',l)
    for (vars,cla) in varlist:
      lit1 = lit % tuple(['X'+str(i) for i in vars])
      #varPool = reduce(lambda x,y: x+';'+y, ['X'+str(i) for i in set(vars)])
      if options.pure_preprocessing:
	sourceclausesstr = '' if len(cla)==0 or isflat else '1 { not closed_subsumed(%s) }' %(reduce(lambda x,y: x+';'+y, [i for i in cla]))
	outputPredicateWithPurePre(lit1,vars,occlist,sourceclausesstr)
      else:
	outputPredicate(lit1,vars)
  
  if not options.use_pred_h and options.consistency_check_negpred:
    for (l,varlist) in neg_predicates.iteritems():
      if options.pure_preprocessing:
	occlist = findOccurrencesInDictString(l)
      lit = VARPLACE_PTRN.sub(r'\1%s',l)
      for (vars,cla) in varlist:
	lit1 = lit % tuple(['X'+str(i) for i in vars])
	if options.pure_preprocessing:
	  sourceclausesstr = '' if len(cla)==0 else '1 { not closed_subsumed(%s) }' %(reduce(lambda x,y: x+';'+y, [i for i in cla]))
	  outputNegPredicateWithPurePre(lit1,vars,occlist,sourceclausesstr)
	else:
	  outputNegPredicate(lit1,vars)
  
def outputFormulaPre(name,isPropositional,isDeskolemized):
  output.write('%% clause %s\n' %(name))
  if isPropositional:
    output.write('#base.\n')
  elif isDeskolemized:
    output.write('#volatile %s.\n' %(INCVAR))
  if options.pure_preprocessing:
    if isDeskolemized:
      output.write(':- not closed_subsumed(_deskol(%s,P1)):P1=1..P:clause_part(%s,P), ' %(name,name))
    else:
      output.write(':- not closed_subsumed(%s), ' %(name))
    #output.write(':- active_%s, ' %(name))
    #output.write(':- not subsumed_%s, ' %(name))
    #output.write(':- active(%s), ' %(name))
  else:
    output.write(':- ')
  global shouldOutputComma
  shouldOutputComma = False

def outputFormulaPost(isPropositional,name2var,clause_name):
  global isDeskolemizedClause
  global lit_place_inquantifier
  
  if isPropositional:
    output.write('.\n')
    #output.write('#cumulative %s.\n\n' %(INCVAR))
  else:
    varPool = reduce(lambda x,y: x+';'+y, ['X'+str(i) for i in set(name2var.itervalues())])
    if options.sort_inference:
      for (var,sortstr) in sorts_of_clause.iteritems():
	output.write(', %s, sort_element(S%d,X%d)' %(sortstr,var,var))
    output.write(', dom(%s).\n' %(varPool))
  if options.pure_preprocessing:
    if not isPropositional:
      output.write('#base.\n')
    if isDeskolemizedClause:
      output.write('clause_part(%s,%d).\n' %(clause_name,lit_place_inquantifier))
      prepro_file.write('clause_part(%s,%d).\n' %(clause_name,lit_place_inquantifier))
    for (p,a,inneg,part) in occurs_list:
      if part==0:
        clsname = clause_name
      else:
        clsname = '_deskol(%s,%d)' %(clause_name,part)
      if inneg:
	output.write('occurs(%s,%d,neg,%s).\n' %(p,a,clsname))
	prepro_file.write('occurs(%s,%d,neg,%s) :- turn(purepreprocessing).\n' %(p,a,clsname))
      else:
	output.write('occurs(%s,%d,pos,%s).\n' %(p,a,clsname))
	prepro_file.write('occurs(%s,%d,pos,%s) :- turn(purepreprocessing).\n' %(p,a,clsname))
    # term occurrances goes only to preprocessing program
    for (f,a,part) in occursterm_list:
      if part==0:
        clsname = clause_name
      else:
        clsname = '_deskol(%s,%d)' %(clause_name,part)
      prepro_file.write('occurs_term(%s,%d,%s) :- turn(purepreprocessing).\n' %(f,a,clsname))
    #output.write('subsumed_%s :- subsumed(%s).\n'%(clause_name,clause_name))
    #output.write('active_%s :- not subsumed(%s).\n'%(clause_name,clause_name))
    output.write('#cumulative %s.\n' %(INCVAR))
  elif isPropositional:
    output.write('#cumulative %s.\n' %(INCVAR))
  if isDeskolemizedClause and not options.pure_preprocessing:
    # because we haven't claused the volatile part yet
    output.write('#cumulative %s.\n' %(INCVAR))
  #output.write('\n')

def outputLiteral(lit):
  global shouldOutputComma
  global inNegationContext
  global isEquality
  
  if shouldOutputComma:
    output.write(', ')
  if isEquality:
    output.write('%s' %(lit))
    isEquality = False
    shouldOutputComma = True
    inNegationContext = False
    return
  if inNegationContext:
    if options.use_pred_h:
      output.write('h(%s)' %(lit))
    else:
      output.write('%s' %(lit))
    inNegationContext = False
  else:
    if options.use_pred_h:
      output.write('not h(%s)' %(lit))
    else:
      output.write('not %s' %(lit))
  shouldOutputComma = True

def outputConjAggregate(currentClause,andClauseNeeded,exivarname):
  global shouldOutputComma
  var = int(ONEVAR_PTRN.match(exivarname).group(1))
  
  if shouldOutputComma:
    output.write(', ')
  if andClauseNeeded:
    headtmp = ''
    for k, groups in groupby(conj_main_lits, lambda x: x[3]):
      i=0
      tmp = ''
      for p in groups:
        i += 1
        tmp += p[1]+','
      if i>1:
        headtmp += '___or(%s),' %(tmp[:-1])
      else:
        headtmp += '%s,' %(tmp[:-1])
    #head = '___and(%s,%s)' %(currentClause,reduce(lambda x,y: x+','+y, [x[1] for x in conj_main_lits]))
    head = '___and(%s,%s)' %(currentClause,headtmp[:-1])
    if len(conj_aggregate)==0:
      #if options.sort_inference:
        #output.write('{ %s:%s:sort_element(S%d,X%d):dom(%s) } 0' %(head,sorts_of_disj[var],var,var,exivarname))
      #else:
      output.write('{ %s:dom(%s) } 0' %(head,exivarname))
    else:
      aggregate_tail = reduce(lambda x,y: x+':'+y, conj_aggregate)
      #if options.sort_inference:
        #output.write('{ %s:%s:sort_element(S%d,X%d):dom(%s):%s } 0' %(head,sorts_of_disj[var],var,var,exivarname,aggregate_tail))
      #else:
      output.write('{ %s:dom(%s):%s } 0' %(head,exivarname,aggregate_tail))
    #and_clause.write('#cumulative %s.\n' %(INCVAR))
    variables = set([int(x) for x in VAR_PTRN.findall(possible_conj_clause_body.getvalue())])
    tmpstr = reduce(lambda x,y: x+';'+y, ['X'+str(x) for x in variables])
    if options.sort_inference:
      and_clause.write('%s :- %s' %(head,possible_conj_clause_body.getvalue())) 
      for (var1,sortstr) in sorts_of_disj.iteritems():
        and_clause.write(', %s, sort_element(S%d,X%d)' %(sortstr,var1,var1))
      and_clause.write(', dom(%s).\n' %(tmpstr))   
    else:
      and_clause.write('%s :- %s, dom(%s).\n' %(head,possible_conj_clause_body.getvalue(),tmpstr))   
  else:
    if len(conj_aggregate)==0:
      #if options.sort_inference:
        #output.write('{ %s:%s:sort_element(S%d,X%d):dom(%s) } 0' %(possible_conj_clause_body.getvalue(),sorts_of_disj[var],var,var,exivarname))
      #else:
      output.write('{ %s:dom(%s) } 0' %(possible_conj_clause_body.getvalue(),exivarname))
    else:
      aggregate_tail = reduce(lambda x,y: x+':'+y, conj_aggregate)
      #if options.sort_inference:
        #output.write('{ %s:%s:sort_element(S%d,X%d):dom(%s):%s } 0' %(possible_conj_clause_body.getvalue(),sorts_of_disj[var],var,var,exivarname,aggregate_tail))
      #else:
      output.write('{ %s:dom(%s):%s } 0' %(possible_conj_clause_body.getvalue(),exivarname,aggregate_tail))
  shouldOutputComma = True
    
def parsePredicateXML(root, name2var):
  # root is the root node for predicate
  # name2var is a mapping from variable names to standart ones {X1,X2,...}
  global isEquality
  global inNegationContext
  global isNonFlatPred
  global curr_clause_name
  
  if not root:
    # propositional atom
    ##base_predicates.add((root.get('name'),0))
    literal = root.get('name')
    occurs_list.append((literal,0,inNegationContext,0))
    if literal in predicates:
      predicates[literal][0][1].add(curr_clause_name)
    else:
      predicates[literal] = [([],set([curr_clause_name]))]
    propositional_predicates.add(root.get('name'))
    return literal
  else:
    if root.get('name') == '=':
      isEquality = True
      eqargs = []
    else:
      base_predicates.add((root.get('name'),len(root)))
      occurs_list.append((root.get('name'),len(root),inNegationContext,0))
      literal = root.get('name')+'('
  
  argplace = 0
  for elem in root.findall('*'):
    argplace += 1
    if elem.tag == 'variable':
      if elem.get('name') not in name2var:
	name2var[elem.get('name')] = len(name2var)+1
      if isEquality:
	# 0: variable 1:term
	eqargs.append((0,'X'+str(name2var[elem.get('name')])))
      else:
	literal += 'X'+str(name2var[elem.get('name')])+','
	if options.sort_inference:
          prepro_file.write('sort_occurs(%s,slot(p(%s,%d),%d),%s) :- turn(sortinference), not closed_subsumed(%s).\n' %(curr_clause_name,root.get('name'),len(root),argplace,'x'+str(name2var[elem.get('name')]),curr_clause_name))
    else:
      #term (in function)
      isNonFlatPred = True
      if isEquality:
	# 0: variable 1:term
	eqargs.append((1,parseTermXML(elem,name2var)))
      else:
        subterm = parseTermXML(elem,name2var)
	literal += subterm+','
	if options.sort_inference:
          variables = [int(x) for x in VAR_PTRN.findall(subterm)]
          t = VARPLACE_PTRN.sub(r'\1%s',TODICT_PTRN.sub(r'\1_',subterm))
          arg1 = t % tuple(['x'+str(i) for i in variables])
          prepro_file.write('sort_occurs(%s,slot(p(%s,%d),%d),%s) :- turn(sortinference), not closed_subsumed(%s).\n' %(curr_clause_name,root.get('name'),len(root),argplace,arg1,curr_clause_name))
          
  
  if options.sort_inference:
    if isEquality and not inNegationContext:
      if eqargs[0][0] == 0:
        arg1 = eqargs[0][1].lower()
      else:
        variables = [int(x) for x in VAR_PTRN.findall(eqargs[0][1])]
        t = VARPLACE_PTRN.sub(r'\1%s',TODICT_PTRN.sub(r'\1_',eqargs[0][1]))
        arg1 = t % tuple(['x'+str(i) for i in variables])
      if eqargs[1][0] == 0:
        arg2 = eqargs[1][1].lower()
      else:
        variables = [int(x) for x in VAR_PTRN.findall(eqargs[1][1])]
        t = VARPLACE_PTRN.sub(r'\1%s',TODICT_PTRN.sub(r'\1_',eqargs[1][1]))
        arg2 = t % tuple(['x'+str(i) for i in variables])
      if eqargs[0][0]+eqargs[1][0] == 0:
        eqtype = 'var2'
      elif eqargs[0][0]+eqargs[1][0] == 1:
        eqtype = 'var1'
      else:
        eqtype = 'term2'
      prepro_file.write('sort_occurs(%s,slot(%s,eq(%s,%s,%s)),%s;%s) :- turn(sortinference), not closed_subsumed(%s).\n' %(curr_clause_name,curr_clause_name,arg1,arg2,eqtype,arg1,arg2,curr_clause_name))
      findSortsFromEq(eqargs,sorts_of_clause,'slot(%s,eq(%s,%s,%s))'%(curr_clause_name,arg1,arg2,eqtype))
        
  if isEquality:
    if eqargs[0][0]+eqargs[1][0] == 0:
      # both are variables
      if inNegationContext:
	literal = eqargs[0][1]+'=='+eqargs[1][1]
      else:
	literal = eqargs[0][1]+'!='+eqargs[1][1]
    elif eqargs[0][0]+eqargs[1][0] == 1:
      # one of them is variable the other one is a term
      if eqargs[0][0] == 0:
	notflat1 = options.assigned_only or len(findOccurrencesInDictString(TODICT_PTRN.sub(r'\1_',eqargs[1][1]))) > 1
	if options.nonflat_function_choices or not notflat1:
	  literal = ('not ' if not inNegationContext else '') + 'assign('+eqargs[1][1]+','+eqargs[0][1]+')'
	else:
          if inNegationContext:
            literal = 'assigned('+eqargs[1][1]+','+eqargs[0][1]+','+INCVAR+')'
          else:
            # create a new variable
            tmpname = '_eq_'+str(len(name2var)+1)
            name2var[tmpname] = len(name2var)+1
            literal = 'assigned('+eqargs[1][1]+',X'+str(name2var[tmpname])+','+INCVAR+'), X'+str(name2var[tmpname])+'!='+eqargs[0][1]
      else:
	notflat1 = options.assigned_only or len(findOccurrencesInDictString(TODICT_PTRN.sub(r'\1_',eqargs[0][1]))) > 1
	if options.nonflat_function_choices or not notflat1:
	  literal = ('not ' if not inNegationContext else '') +'assign('+eqargs[0][1]+','+eqargs[1][1]+')'
	else:
          if inNegationContext:
            literal = 'assigned('+eqargs[0][1]+','+eqargs[1][1]+','+INCVAR+')'
          else:
            # create a new variable
            tmpname = '_eq_'+str(len(name2var)+1)
            name2var[tmpname] = len(name2var)+1
            literal = 'assigned('+eqargs[0][1]+',X'+str(name2var[tmpname])+','+INCVAR+'), X'+str(name2var[tmpname])+'!='+eqargs[1][1]
      #if not inNegationContext:
	#literal = 'not '+literal
    elif eqargs[0][0]+eqargs[1][0] == 2:
      # both of them are terms
      tmpname = '_eq_'+str(len(name2var)+1)
      name2var[tmpname] = len(name2var)+1
      notflat1 = options.assigned_only or len(findOccurrencesInDictString(TODICT_PTRN.sub(r'\1_',eqargs[0][1]))) > 1
      notflat2 = options.assigned_only or len(findOccurrencesInDictString(TODICT_PTRN.sub(r'\1_',eqargs[1][1]))) > 1
      if not inNegationContext:
	if options.nonflat_function_choices:
	  literal = 'assign('+eqargs[0][1]+',X'+str(name2var[tmpname])+'), not assign('+eqargs[1][1]+',X'+str(name2var[tmpname])+')'
	else:
	  if notflat1:
	    l1 = 'assigned('+eqargs[0][1]+',X'+str(name2var[tmpname])+','+INCVAR+')'
	  else:
	    l1 = 'assign('+eqargs[0][1]+',X'+str(name2var[tmpname])+')'
	  if notflat2:
	    l2 = ', not assigned('+eqargs[1][1]+',X'+str(name2var[tmpname])+','+INCVAR+')'
	  else:
	    l2 = ', not assign('+eqargs[1][1]+',X'+str(name2var[tmpname])+')'
	  #literal = 'assigned('+eqargs[0][1]+',X'+str(name2var[tmpname])+','+INCVAR+'), not assigned('+eqargs[1][1]+',X'+str(name2var[tmpname])+','+INCVAR+')'
	  literal = l1+l2
      else:
	if options.nonflat_function_choices:
	  literal = 'assign('+eqargs[0][1]+',X'+str(name2var[tmpname])+'), assign('+eqargs[1][1]+',X'+str(name2var[tmpname])+')'
	else:
	  if notflat1:
	    l1 = 'assigned('+eqargs[0][1]+',X'+str(name2var[tmpname])+','+INCVAR+')'
	  else:
	    l1 = 'assign('+eqargs[0][1]+',X'+str(name2var[tmpname])+')'
	  if notflat2:
	    l2 = ', assigned('+eqargs[1][1]+',X'+str(name2var[tmpname])+','+INCVAR+')'
	  else:
	    l2 = ', assign('+eqargs[1][1]+',X'+str(name2var[tmpname])+')'
	  #literal = 'assigned('+eqargs[0][1]+',X'+str(name2var[tmpname])+','+INCVAR+'), assigned('+eqargs[1][1]+',X'+str(name2var[tmpname])+','+INCVAR+')'
	  literal = l1+l2
    return literal
  else:
    literal = literal[:-1]+')'
  
  todict = TODICT_PTRN.sub(r'\1_',literal)
  variables = [int(x) for x in VAR_PTRN.findall(literal)]
  insertToDict(todict,variables,predicates, True,curr_clause_name)
  if inNegationContext and isNonFlatPred:
    insertToDict(todict,variables,neg_predicates, True,curr_clause_name)
    base_neg_predicates.add((root.get('name'),len(root)))
  elif not inNegationContext and isNonFlatPred:
    insertToDict(todict,variables,pos_nonflat_predicates)
    base_pos_predicates.add((root.get('name'),len(root)))
  #if todict not in predicates:
    #predicates[todict] = [variables]
  #else:
    #for i in range(0,len(predicates[todict])):
      #if isMoreGeneral(predicates[todict][i],variables):
	#return literal
      #elif isMoreGeneral(variables,predicates[todict][i]):
	#predicates[todict][i] = variables
	#return literal
    #predicates[todict].append(variables)
  return literal

def outputConjLiteral(lit):
  global shouldOutputComma
  global inNegationContext
  global isEquality
  
  if shouldOutputComma:
    output.write(', ')
  if isEquality:
    output.write('%s' %(lit))
    isEquality = False
    shouldOutputComma = True
    inNegationContext = False
    return
  if inNegationContext:
    if options.use_pred_h:
      output.write('not h(%s)' %(lit))
    else:
      output.write('not %s' %(lit))
    inNegationContext = False
  else:
    if options.use_pred_h:
      output.write('h(%s)' %(lit))
    else:
      output.write('%s' %(lit))
  shouldOutputComma = True

def parseConjPredicateXML(root, name2var):
  # root is the root node for predicate
  # name2var is a mapping from variable names to standart ones {X1,X2,...}
  global isEquality
  global inNegationContext
  global isNonFlatPred
  global curr_clause_name
  global existential_variable
  global lit_place_inquantifier
  global isInDisjInQuantifier
  
  #lit_place_inquantifier += 1
  
  if not root:
    # propositional atom
    ##base_predicates.add((root.get('name'),0))
    literal = root.get('name')
    occurs_list.append((literal,0,inNegationContext,lit_place_inquantifier))
    if literal in predicates:
      predicates[literal][0][1].add(curr_clause_name)
    else:
      predicates[literal] = [([],set([curr_clause_name]))]
    propositional_predicates.add(root.get('name'))
    andname = 'neg(%s)'%(literal) if inNegationContext else literal
    conj_main_lits.append((literal,andname,True,lit_place_inquantifier))
    outputConjLiteral(literal)
    return literal
  else:
    if root.get('name') == '=':
      isEquality = True
      eqargs = []
    else:
      base_predicates.add((root.get('name'),len(root)))
      occurs_list.append((root.get('name'),len(root),inNegationContext,lit_place_inquantifier))
      literal = root.get('name')+'('
  
  argplace = 0
  for elem in root.findall('*'):
    argplace += 1
    if elem.tag == 'variable':
      if elem.get('name') not in name2var:
        name2var[elem.get('name')] = len(name2var)+1
      if isEquality:
        # 0: variable 1:term
        eqargs.append((0,'X'+str(name2var[elem.get('name')])))
      else:
        literal += 'X'+str(name2var[elem.get('name')])+','
        if options.sort_inference:
          prepro_file.write('sort_occurs(%s,slot(p(%s,%d),%d),%s) :- turn(sortinference), not closed_subsumed(_deskol(%s,%d)).\n' %(curr_clause_name,root.get('name'),len(root),argplace,'x'+str(name2var[elem.get('name')]),curr_clause_name,lit_place_inquantifier))
          if options.ghostfunc_sorts and name2var[elem.get('name')] == name2var[existential_variable]:
            prepro_file.write('sort_occurs(%s,slot(f(%s,1),2),%s) :- turn(sortinference), not closed_subsumed(%s).\n' %(curr_clause_name, '_var'+existential_variable,'x'+str(name2var[elem.get('name')]),curr_clause_name))
    else:
      #term (in function)
      isNonFlatPred = True
      if isEquality:
        # 0: variable 1:term
        eqargs.append((1,parseTermXML(elem,name2var)))
      else:
        subterm = parseTermXML(elem,name2var)
        literal += subterm+','
        if options.sort_inference:
          variables = [int(x) for x in VAR_PTRN.findall(subterm)]
          t = VARPLACE_PTRN.sub(r'\1%s',TODICT_PTRN.sub(r'\1_',subterm))
          arg1 = t % tuple(['x'+str(i) for i in variables])
          prepro_file.write('sort_occurs(%s,slot(p(%s,%d),%d),%s) :- turn(sortinference), not closed_subsumed(_deskol(%s,%d)).\n' %(curr_clause_name,root.get('name'),len(root),argplace,arg1,curr_clause_name,lit_place_inquantifier))

  if options.sort_inference:
    if isEquality and not inNegationContext:
      if eqargs[0][0] == 0:
        arg1 = eqargs[0][1].lower()
      else:
        variables = [int(x) for x in VAR_PTRN.findall(eqargs[0][1])]
        t = VARPLACE_PTRN.sub(r'\1%s',TODICT_PTRN.sub(r'\1_',eqargs[0][1]))
        arg1 = t % tuple(['x'+str(i) for i in variables])
      if eqargs[1][0] == 0:
        arg2 = eqargs[1][1].lower()
      else:
        variables = [int(x) for x in VAR_PTRN.findall(eqargs[1][1])]
        t = VARPLACE_PTRN.sub(r'\1%s',TODICT_PTRN.sub(r'\1_',eqargs[1][1]))
        arg2 = t % tuple(['x'+str(i) for i in variables])
      if eqargs[0][0]+eqargs[1][0] == 0:
        eqtype = 'var2'
      elif eqargs[0][0]+eqargs[1][0] == 1:
        eqtype = 'var1'
      else:
        eqtype = 'term2'
      prepro_file.write('sort_occurs(%s,slot(%s,eq(%s,%s,%s)),%s;%s) :- turn(sortinference), not closed_subsumed(_deskol(%s,%d)).\n' %(curr_clause_name,curr_clause_name,arg1,arg2,eqtype,arg1,arg2,curr_clause_name,lit_place_inquantifier))
      if eqargs[0][0]+eqargs[1][0] != 0:
        #no need to call for the both variables case since it wont be in the and clause
        findSortsFromEq(eqargs,sorts_of_disj,'slot(%s,eq(%s,%s,%s))'%(curr_clause_name,arg1,arg2,eqtype))
      # above check becomes problematic for i_0_578 in CSR078+3
      #findSortsFromEq(eqargs,sorts_of_disj,'slot(%s,eq(%s,%s,%s))'%(curr_clause_name,arg1,arg2,eqtype))
      if options.ghostfunc_sorts:
        if eqargs[0][0]==0 and int(ONEVAR_PTRN.match(eqargs[0][1]).group(1)) == name2var[existential_variable]:
          prepro_file.write('sort_occurs(%s,slot(f(%s,1),2),%s) :- turn(sortinference), not closed_subsumed(%s).\n' %(curr_clause_name, '_var'+existential_variable,arg1,curr_clause_name))
        if eqargs[1][0]==0 and int(ONEVAR_PTRN.match(eqargs[1][1]).group(1)) == name2var[existential_variable]:
          prepro_file.write('sort_occurs(%s,slot(f(%s,1),2),%s) :- turn(sortinference), not closed_subsumed(%s).\n' %(curr_clause_name, '_var'+existential_variable,arg2,curr_clause_name))
      
  if isEquality:
    tmpname = None
    if eqargs[0][0]+eqargs[1][0] == 0:
      # both are variables
      if inNegationContext:
        literal = eqargs[0][1]+'!='+eqargs[1][1]
      else:
        literal = eqargs[0][1]+'=='+eqargs[1][1]
    elif eqargs[0][0]+eqargs[1][0] == 1:
      # one of them is variable the other one is a term
      if eqargs[0][0] == 0:
        notflat1 = options.assigned_only or len(findOccurrencesInDictString(TODICT_PTRN.sub(r'\1_',eqargs[1][1]))) > 1
        if options.nonflat_function_choices or not notflat1:
          literal = ('not ' if inNegationContext else '') + 'assign('+eqargs[1][1]+','+eqargs[0][1]+')'
        else:
          if not inNegationContext:
            literal = 'assigned('+eqargs[1][1]+','+eqargs[0][1]+','+INCVAR+')'
          else:
            # create a new variable
            tmpname = '_eq_'+str(len(name2var)+1)
            name2var[tmpname] = len(name2var)+1
            literal = 'assigned('+eqargs[1][1]+',X'+str(name2var[tmpname])+','+INCVAR+'), X'+str(name2var[tmpname])+'!='+eqargs[0][1]
      else:
        notflat1 = options.assigned_only or len(findOccurrencesInDictString(TODICT_PTRN.sub(r'\1_',eqargs[0][1]))) > 1
        if options.nonflat_function_choices or not notflat1:
          literal = ('not ' if inNegationContext else '') +'assign('+eqargs[0][1]+','+eqargs[1][1]+')'
        else:
          if not inNegationContext:
            literal = 'assigned('+eqargs[0][1]+','+eqargs[1][1]+','+INCVAR+')'
          else:
            # create a new variable
            tmpname = '_eq_'+str(len(name2var)+1)
            name2var[tmpname] = len(name2var)+1
            literal = 'assigned('+eqargs[0][1]+',X'+str(name2var[tmpname])+','+INCVAR+'), X'+str(name2var[tmpname])+'!='+eqargs[1][1]
      #if not inNegationContext:
        #literal = 'not '+literal
    elif eqargs[0][0]+eqargs[1][0] == 2:
      # both of them are terms
      tmpname = '_eq_'+str(len(name2var)+1)
      name2var[tmpname] = len(name2var)+1
      notflat1 = options.assigned_only or len(findOccurrencesInDictString(TODICT_PTRN.sub(r'\1_',eqargs[0][1]))) > 1
      notflat2 = options.assigned_only or len(findOccurrencesInDictString(TODICT_PTRN.sub(r'\1_',eqargs[1][1]))) > 1
      if inNegationContext:
        if options.nonflat_function_choices:
          literal = 'assign('+eqargs[0][1]+',X'+str(name2var[tmpname])+'), not assign('+eqargs[1][1]+',X'+str(name2var[tmpname])+')'
        else:
          if notflat1:
            l1 = 'assigned('+eqargs[0][1]+',X'+str(name2var[tmpname])+','+INCVAR+')'
          else:
            l1 = 'assign('+eqargs[0][1]+',X'+str(name2var[tmpname])+')'
          if notflat2:
            l2 = ', not assigned('+eqargs[1][1]+',X'+str(name2var[tmpname])+','+INCVAR+')'
          else:
            l2 = ', not assign('+eqargs[1][1]+',X'+str(name2var[tmpname])+')'
          #literal = 'assigned('+eqargs[0][1]+',X'+str(name2var[tmpname])+','+INCVAR+'), not assigned('+eqargs[1][1]+',X'+str(name2var[tmpname])+','+INCVAR+')'
          literal = l1+l2
      else:
        if options.nonflat_function_choices:
          literal = 'assign('+eqargs[0][1]+',X'+str(name2var[tmpname])+'), assign('+eqargs[1][1]+',X'+str(name2var[tmpname])+')'
        else:
          if notflat1:
            l1 = 'assigned('+eqargs[0][1]+',X'+str(name2var[tmpname])+','+INCVAR+')'
          else:
            l1 = 'assign('+eqargs[0][1]+',X'+str(name2var[tmpname])+')'
          if notflat2:
            l2 = ', assigned('+eqargs[1][1]+',X'+str(name2var[tmpname])+','+INCVAR+')'
          else:
            l2 = ', assign('+eqargs[1][1]+',X'+str(name2var[tmpname])+')'
          #literal = 'assigned('+eqargs[0][1]+',X'+str(name2var[tmpname])+','+INCVAR+'), assigned('+eqargs[1][1]+',X'+str(name2var[tmpname])+','+INCVAR+')'
          literal = l1+l2
    #return literal
  else:
    literal = literal[:-1]+')'

  if not isEquality:
    findSortsFromElement(literal,sorts_of_disj,'pred')
  
  if isEquality and eqargs[0][0]+eqargs[1][0] == 0 and not isInDisjInQuantifier:
    # equality with two variable arguments
    conj_aggregate.append(literal)
    isEquality = False
    inNegationContext = False
    return literal
  else:
    if isEquality:
      andname = 'neg(' if inNegationContext else '' 
      andname += '___eq(%s,%s' %(eqargs[0][1],eqargs[1][1])
      if tmpname != None:
        andname += ',%s)' %('X'+str(name2var[tmpname]))
      else:
        andname += ')'
      andname += ')' if inNegationContext else ''
      conj_main_lits.append((literal,andname,True,lit_place_inquantifier))
      outputConjLiteral(literal)
      # delete the tmpname variable
      if tmpname != None:
        del name2var[tmpname]
      return literal
    else:
      if inNegationContext:
        andname = 'neg(%s)'%(literal)
      else:
        andname = literal
      conj_main_lits.append((literal,andname,False,lit_place_inquantifier))
      #outputConjLiteral(literal)
      # SEU288+1 bug outputConjLiteral clears the inNegationContext before
      # the literal is put into the occurs dictionary
      
  
  todict = TODICT_PTRN.sub(r'\1_',literal)
  variables = [int(x) for x in VAR_PTRN.findall(literal)]
  insertToDict(todict,variables,predicates,True,curr_clause_name)
  if inNegationContext and isNonFlatPred:
    insertToDict(todict,variables,neg_predicates, True,curr_clause_name)
    base_neg_predicates.add((root.get('name'),len(root)))
  elif not inNegationContext and isNonFlatPred:
    insertToDict(todict,variables,pos_nonflat_predicates)
    base_pos_predicates.add((root.get('name'),len(root)))
  #if todict not in predicates:
    #predicates[todict] = [variables]
  #else:
    #for i in range(0,len(predicates[todict])):
      #if isMoreGeneral(predicates[todict][i],variables):
        #return literal
      #elif isMoreGeneral(variables,predicates[todict][i]):
        #predicates[todict][i] = variables
        #return literal
    #predicates[todict].append(variables)
  outputConjLiteral(literal)  
  return literal

def insertToDict(todict, variables, whichdict, withsourceclauses = False, sourceclause = ''):
  if todict not in whichdict:
    if withsourceclauses and sourceclause != '':
      whichdict[todict] = [(variables,set([sourceclause]))]
    elif withsourceclauses and sourceclause == '':
      whichdict[todict] = [(variables,set())]
    else:
      whichdict[todict] = [variables]
  else:
    if withsourceclauses:
      for i in range(0,len(whichdict[todict])):
	if isMoreGeneral(whichdict[todict][i][0],variables):
	  if sourceclause != '':
	    whichdict[todict][i][1].add(sourceclause)
	  return
	elif isMoreGeneral(variables,whichdict[todict][i][0]):
	  if sourceclause != '':
	    whichdict[todict][i][1].add(sourceclause)
	  sources = whichdict[todict][i][1]
	  whichdict[todict][i] = (variables,sources)
	  return
      whichdict[todict].append((variables,set([sourceclause]) if sourceclause!='' else set()))
    else:
      for i in range(0,len(whichdict[todict])):
	if isMoreGeneral(whichdict[todict][i],variables):
	  return
	elif isMoreGeneral(variables,whichdict[todict][i]):
	  whichdict[todict][i] = variables
	  return
      whichdict[todict].append(variables)
    

def parseTermXML(root, name2var):
  # root is the root node for function (which can be constant or (deep)function)
  # name2var is a mapping from variable names to standart ones {X1,X2,...}
  global curr_clause_name
  global inQuantifier
  global existential_variable
  global lit_place_inquantifier
  
  if not root:
    # above checks whether root has children or not
    #constant
    term = root.get('name')
    constants[term] = True
    if inQuantifier:
      occursterm_list.append((term,0,lit_place_inquantifier))
    else:
      occursterm_list.append((term,0,0))
    if options.sort_inference:
      if inQuantifier:
        prepro_file.write('sort_occurs(%s,slot(f(%s,0),1),%s) :- turn(sortinference), not closed_subsumed(_deskol(%s,%d)).\n' %(curr_clause_name,root.get('name'),root.get('name'),curr_clause_name,lit_place_inquantifier))
      else:
        prepro_file.write('sort_occurs(%s,slot(f(%s,0),1),%s) :- turn(sortinference), not closed_subsumed(%s).\n' %(curr_clause_name,root.get('name'),root.get('name'),curr_clause_name))
    return term
  else:
    base_functions.add((root.get('name'),len(root)))
    if inQuantifier:
      occursterm_list.append((root.get('name'),len(root),lit_place_inquantifier))
    else:
      occursterm_list.append((root.get('name'),len(root),0))
    term = root.get('name')+'('
  
  argplace = 0
  for  elem in root.findall('*'):
    argplace += 1
    if elem.tag == 'variable':
      if elem.get('name') not in name2var:
	name2var[elem.get('name')] = len(name2var)+1
      term += 'X'+str(name2var[elem.get('name')])+','
      if options.sort_inference:
        if inQuantifier:
          prepro_file.write('sort_occurs(%s,slot(f(%s,%d),%d),%s) :- turn(sortinference), not closed_subsumed(_deskol(%s,%d)).\n' %(curr_clause_name,root.get('name'),len(root),argplace,'x'+str(name2var[elem.get('name')]),curr_clause_name,lit_place_inquantifier))
        else:
          prepro_file.write('sort_occurs(%s,slot(f(%s,%d),%d),%s) :- turn(sortinference), not closed_subsumed(%s).\n' %(curr_clause_name,root.get('name'),len(root),argplace,'x'+str(name2var[elem.get('name')]),curr_clause_name))
        if options.ghostfunc_sorts and inQuantifier and name2var[elem.get('name')] == name2var[existential_variable]:
          prepro_file.write('sort_occurs(%s,slot(f(%s,1),2),%s) :- turn(sortinference), not closed_subsumed(%s).\n' %(curr_clause_name, '_var'+existential_variable,'x'+str(name2var[elem.get('name')]),curr_clause_name))
    else:
      #function term (constant or functional)
      subterm = parseTermXML(elem,name2var)
      term += subterm+','
      if options.sort_inference:
        variables = [int(x) for x in VAR_PTRN.findall(subterm)]
        t = VARPLACE_PTRN.sub(r'\1%s',TODICT_PTRN.sub(r'\1_',subterm))
        arg1 = t % tuple(['x'+str(i) for i in variables])
        if inQuantifier:
          prepro_file.write('sort_occurs(%s,slot(f(%s,%d),%d),%s) :- turn(sortinference), not closed_subsumed(_deskol(%s,%d)).\n' %(curr_clause_name,root.get('name'),len(root),argplace,arg1,curr_clause_name,lit_place_inquantifier))
        else:
          prepro_file.write('sort_occurs(%s,slot(f(%s,%d),%d),%s) :- turn(sortinference), not closed_subsumed(%s).\n' %(curr_clause_name,root.get('name'),len(root),argplace,arg1,curr_clause_name))
        
  term = term[:-1]+')'
  
  if options.sort_inference:
    variables = [int(x) for x in VAR_PTRN.findall(term)]
    t = VARPLACE_PTRN.sub(r'\1%s',TODICT_PTRN.sub(r'\1_',term))
    arg1 = t % tuple(['x'+str(i) for i in variables])
    if inQuantifier:
      prepro_file.write('sort_occurs(%s,slot(f(%s,%d),%d),%s) :- turn(sortinference), not closed_subsumed(_deskol(%s,%d)).\n' %(curr_clause_name,root.get('name'),len(root),len(root)+1,arg1,curr_clause_name,lit_place_inquantifier))
    else:
      prepro_file.write('sort_occurs(%s,slot(f(%s,%d),%d),%s) :- turn(sortinference), not closed_subsumed(%s).\n' %(curr_clause_name,root.get('name'),len(root),len(root)+1,arg1,curr_clause_name))
    
  todict = TODICT_PTRN.sub(r'\1_',term)
  variables = [int(x) for x in VAR_PTRN.findall(term)]
  insertToDict(todict,variables, functional_terms, True, curr_clause_name)
  #if todict not in functional_terms:
    #functional_terms[todict] = [variables]
  #else:
    #for i in range(0,len(functional_terms[todict])):
      #if isMoreGeneral(functional_terms[todict][i],variables):
	#return term
      #elif isMoreGeneral(variables,functional_terms[todict][i]):
	#functional_terms[todict][i] = variables
	#return term
    #functional_terms[todict].append(variables)
  return term

def isMoreGeneral(general,specific):
  # general and specific are lists of variable bindings
  
  mapping = dict()
  for i in range(0,len(general)):
    if general[i] not in mapping:
      mapping[general[i]] = specific[i]
    elif mapping[general[i]] != specific[i]:
      return False
  return True

def findSortsFromElement(element,sorts,typ):
  # sorts is a dictionary from variable number to sort string
  # typ is the type of the element: pred or func
  
  args = findArguments(element)
  name = element[:element.find('(')]
  arity = len(args)
  if typ == 'pred':
    typstr = 'p'
  elif typ == 'func':
    typstr = 'f'
  
  argplace = 0
  for a in args:
    argplace += 1
    r = ONEVAR_PTRN.match(a)
    if r:
      if int(r.group(1)) in sorts:
        continue
      sorts[int(r.group(1))] = 'in_sort(slot(%s(%s,%d),%d),S%s)' %(typstr,name,arity,argplace,r.group(1))
      continue
    r = FUNCNAME_PTRN.match(a)
    if r:
      findSortsFromElement(a,sorts,'func')
      
def findSortsFromEq(eqargs,sorts,slot):
  # for the case X = f(...) there is no need to find the sort for X since it's value of a function!
  if eqargs[0][0]+eqargs[1][0] == 0:
    # both are variables
    v1 = int(ONEVAR_PTRN.match(eqargs[0][1]).group(1))
    v2 = int(ONEVAR_PTRN.match(eqargs[1][1]).group(1))
    if v1 not in sorts:
      sorts[v1] = 'in_sort(%s,S%d)' %(slot,v1)
    if v2 not in sorts:
      sorts[v2] = 'in_sort(%s,S%d)' %(slot,v2)
    return
  #if eqargs[0][0] == 0:
    #v1 = int(ONEVAR_PTRN.match(eqargs[0][1]).group(1))
    #if v1 not in sorts:
      #sorts[v1] = 'in_sort(%s,S%d)' %(slot,v1)
  #if eqargs[1][0] == 0:
    #v2 = int(ONEVAR_PTRN.match(eqargs[1][1]).group(1))
    #if v2 not in sorts:
      #sorts[v2] = 'in_sort(%s,S%d)' %(slot,v2)
  if eqargs[0][0] == 1:
    findSortsFromElement(eqargs[0][1],sorts,'func')
  if eqargs[1][0] == 1:
    findSortsFromElement(eqargs[1][1],sorts,'func')
  
def findArguments(element):
  level = 0
  output = []
  start = 0
  curr = 0
  ptrn = re.compile('[\(\),]')
  
  res = ptrn.search(element,curr)
  while  res != None:
    f = res.group()
    if f == '(':
      level += 1
      if level == 1:
	start = res.start() + 1
    elif f == ',':
      if level == 1:
	output.append(element[start:res.start()])
	start = res.start() + 1
    elif f == ')':
      if level == 1:
	output.append(element[start:res.start()])
	start = res.start() + 1
      level -= 1
        
    curr = res.start() + 1
    res = ptrn.search(element,curr)
  
  return output
    
def findOccurrencesInDictString(element):
  stack = []
  output = []
  current = ''
  currentarity = 0
  onIdentifier = False
  i = 0
  while i != len(element):
    if element[i] == '(':
      if current != '':
	stack.append((current,currentarity))
      current = element[idstart:i]
      currentarity = 0
      onIdentifier = False
      i += 1
      continue
    #if element[i:i+2] == '_,':
      #currentarity += 1
      #i += 2
      #continue
    elif element[i] == '_':
      #currentarity += 1
      i += 1
      continue
    elif element[i] == ',':
      currentarity += 1
      if onIdentifier:
	output.append((element[idstart:i],0))
	onIdentifier = False
      i += 1
      continue
    elif element[i] == ')':
      currentarity += 1
      if onIdentifier:
	output.append((element[idstart:i],0))
	onIdentifier = False
      output.append((current,currentarity))
      if len(stack) == 0:
	return output
      (current,currentarity) = stack.pop()
      i += 1
      continue
    else:
      if not onIdentifier:
	onIdentifier = True 
	idstart = i
      i += 1
      continue
  if len(output) == 0:
    output.append((element[idstart:i],currentarity))
    return output
      
def checkTrueFalseOption(option, opt_str, value, parser):
  if value == 'true':
    setattr(parser.values, option.dest, True)
  elif value == 'false':
    setattr(parser.values, option.dest, False)
  else:
    raise OptionValueError("%s option takes true|false as argument" % opt_str)

def outputAuxSortMax():
  output.write('#base.\n\n')
  
  for (pred,arity) in base_predicates:
    output.write('aux_sortmax(p(%s,%d),m(%s)) :- ' %(pred,arity,reduce(lambda x,y:x+','+y,['M'+str(i) for i in range(1,arity+1)])))
    for i in xrange(1,arity+1):
      output.write('in_sort(slot(p(%s,%d),%d),S%d), sort_max(S%d,M%d), ' %(pred,arity,i,i,i,i))
    output.write('1==1.\n')
    
  for (func,arity) in base_functions:
    output.write('aux_sortmax(f(%s,%d),m(%s)) :- ' %(func,arity,reduce(lambda x,y:x+','+y,['M'+str(i) for i in range(1,arity+1)])))
    for i in xrange(1,arity+1):
      output.write('in_sort(slot(f(%s,%d),%d),S%d), sort_max(S%d,M%d), ' %(func,arity,i,i,i,i))
    output.write('1==1.\n')
    
  output.write('#show aux_sortmax/2.\n')

def outputInputPredicatesFunctions():
  output.write('#base.\n\n')
  
  for (pred,arity) in base_predicates:
    output.write('input_predicate(%s,%d).\n' %(pred,arity))
    
  for (func,arity) in base_functions:
    output.write('input_function(%s,%d).\n' %(func,arity))
    
  for c in constants:
    output.write('input_function(%s,0).\n' %(c))
    
  output.write('#show input_predicate/2.\n#show input_function/2.\n')

def processOutputAS():
  global iclingo_main_process
  global has_conjecture
  
  out = iclingo_main_process.communicate()
  
  # check whether it is sat or unsat
  r = SATUNSAT_PTRN.search(out[0])
  if r:
    if r.group(1) == 'SATISFIABLE':
      if has_conjecture:
        sys.stdout.write('% SZS status CounterSatisfiable\n')
      else:
        sys.stdout.write('% SZS status Satisfiable\n')
    elif r.group(1) == 'UNSATISFIABLE':
      if has_conjecture:
        sys.stdout.write('% SZS status Theorem\n')
      else:
        sys.stdout.write('% SZS status Unsatisfiable\n')
      return
  else:
    # should I output error or gaveup?
    sys.stdout.write('% SZS status GaveUp\n')
    #sys.out.write(out[0])
    #sys.out.write(out[1])
    return
  
  ans = re.compile('Answer.*\n(.*)\n').search(out[0]).group(1)
  # now output the model
  sys.stdout.write('% SZS output start Model\n')
  elements = []
  for e in re.compile('(?:^| )dom\((\d+)\)').finditer(ans):
    elements.append(int(e.group(1)))
  elements.sort()
  domsize = len(elements)
  sys.stdout.write('finite domain: {%s}\n' %(reduce(lambda x,y: x+','+y,[str(i) for i in elements])))
  
  for c in constants:
    if (c,0) in subsumed_terms:
      sys.stdout.write('%s = 1 *s*\n' %(c))
    else:
      r = re.compile('(?:^| )assign\(%s,(\d+)\)'%(c)).search(ans)
      sys.stdout.write('%s = %s\n' %(c,r.group(1)))
  
  for (func,arity) in base_functions:
    sys.stdout.write('%s/%d:\n' %(func,arity))
    if (func,arity) in subsumed_terms:
      sys.stdout.write('\t(%s) = 1 *s*\n' %(reduce(lambda x,y: x+','+y,['X'+str(i) for i in range(0,arity)])))
    else:
      ptrn = '(?:^| )assign\(%s\((%s)\),%s\)' %(func,reduce(lambda x,y: x+','+y,['\d+' for i in range(0,arity)]),'(\d+)')
      for r in re.compile(ptrn).finditer(ans):
        sys.stdout.write('\t(%s) = %s\n' %(r.group(1), r.group(2)))
      if options.sort_inference:  
	ptrn = '(?:^| )aux_sortmax\(f\(%s,%d\),m\(%s\)\)' %(func,arity,reduce(lambda x,y: x+','+y,['(\d+|#supremum)' for i in range(0,arity)]))
	r = re.compile(ptrn).search(ans)
	tmp = ['X'+str(i) for i in range(1,arity+1)]
	for i in xrange(1,arity+1):
	  if r.group(i) != '#supremum' and int(r.group(i)) < domsize:
	    sys.stdout.write('\t(%s) = ' %(reduce(lambda x,y: x+','+y,tmp)))
	    if r.group(i) == '0':
	      sys.stdout.write('1\n')
	      break
	    tmp[i-1] = r.group(i)
	    sys.stdout.write('%s(%s) : X%d>%s\n' %(func,reduce(lambda x,y: x+','+y,tmp),i,r.group(i)))
	    tmp[i-1] = 'X'+str(i)
	
        
  for pred in propositional_predicates:
    sys.stdout.write('%s/0:\n' %(pred))
    r = re.compile('(?:^| )pure\(%s,0,(pos|neg)\)'%(pred)).search(ans)
    if r:
      sys.stdout.write('\t%s\n'%('True' if r.group(1)=='pos' else 'False'))
    else:
      if options.use_pred_h:
        r = re.compile('(?:^| )h\(%s\)'%(pred)).search(ans)
      else:
        r = re.compile('(?:^| )%s '%(pred)).search(ans)
      if r:
        sys.stdout.write('\tTrue\n')
      else:
        sys.stdout.write('\tFalse\n')
        
  for (pred,arity) in base_predicates:
    sys.stdout.write('%s/%d:\n' %(pred,arity))
    if options.use_pred_h:
      ptrn = '(?:^| )h\(%s\((%s)\)\)' %(pred,reduce(lambda x,y: x+','+y,['\d+' for i in range(0,arity)]))
    else:
      ptrn = '(?:^| )%s\((%s)\)' %(pred,reduce(lambda x,y: x+','+y,['\d+' for i in range(0,arity)]))
    check_pure = True
    for r in re.compile(ptrn).finditer(ans):
      check_pure = False
      sys.stdout.write('\t(%s) <=> True\n' %(r.group(1)))
    if check_pure:
      r = re.compile('(?:^| )pure\(%s,%d,(pos|neg)\)'%(pred,arity)).search(ans)
      if r:
        sys.stdout.write('\t(%s) <=> %s *p*\n' %(reduce(lambda x,y: x+','+y,['X'+str(i) for i in range(0,arity)]),'True' if r.group(1)=='pos' else 'False'))
    elif options.sort_inference:
      ptrn = '(?:^| )aux_sortmax\(p\(%s,%d\),m\(%s\)\)' %(pred,arity,reduce(lambda x,y: x+','+y,['(\d+|#supremum)' for i in range(0,arity)]))
      r = re.compile(ptrn).search(ans)
      tmp = ['X'+str(i) for i in range(1,arity+1)]
      for i in xrange(1,arity+1):
        if r.group(i) != '#supremum' and int(r.group(i)) < domsize:
          sys.stdout.write('\t(%s) <=> ' %(reduce(lambda x,y: x+','+y,tmp)))
          tmp[i-1] = r.group(i)
          sys.stdout.write('%s(%s) : X%d>%s\n' %(pred,reduce(lambda x,y: x+','+y,tmp),i,r.group(i)))
          tmp[i-1] = 'X'+str(i)
            
  sys.stdout.write('% SZS output end Model\n')
  
def setSignalHandlers():
  catch = ['SIGXCPU','SIGALRM','SIGINT']
  for i in [x for x in dir(signal) if x.startswith("SIG")]:
    if i in catch:
      signum = getattr(signal,i)
      signal.signal(signum,signalHandler)
      
def signalHandler(signum, stack):
  global prepro_file
  if prepro_file:
    #print 'DEBUG', prepro_file.name
    os.remove(os.path.abspath(prepro_file.name))
  sys.exit()

def main():
  setSignalHandlers()
  
  global options
  global output
  
  usage = 'usage: %prog [options] tptp-cnf-xml-input'
  parser = OptionParser(usage=usage)
  parser.add_option("-s", "--symbreak", dest="symbreak", default=True, type="string",
    action="callback", callback= checkTrueFalseOption, help="set symmetry break for constants true|false (Default: true)", 
    metavar='true|false')
  parser.add_option("-c", "--canonical-form", dest="canonical_form", type="choice", action="store",
    choices=["None","Normal","NormalInPaper","Fat"], default='Normal', metavar='None|Normal|NormalInPaper|Fat',
    help='force a canonical form for constants in symmetry breaking. None: do not force, Normal: without cardinality literal, \
NormalInPaper: one constraint for each constant not for adjacent ones, Fat: with cardinality literal (Default: Normal)')
  parser.add_option("-d", "--dom-in-consistency-checks", dest="dom_in_consistency", default=True, type="string",
    action="callback", callback= checkTrueFalseOption, help="set adding dom predicates to consistency checks for eliminating redundant rules true|false (Default: true)", 
    metavar='true|false')
  parser.add_option("-n", "--consistency-check-negpred", dest="consistency_check_negpred", default=True, type="string",
    action="callback", callback= checkTrueFalseOption, help="set generating consistency checks for negative predicates also true|false (Default: true)", 
    metavar='true|false')
  parser.add_option("--use-pred-and-h", dest="use_pred_h", default=False, type="string",
    action="callback", callback= checkTrueFalseOption, help="set using pred and h predicates for literals true|false (Default: false)", 
    metavar='true|false')
  parser.add_option("--use-not-assign-in-consistencies", dest="use_not_assign", default=True, type="string",
    action="callback", callback= checkTrueFalseOption, help="set using not assign in a cardinality literal in consistency checks true|false for experimenting with body literal ordering of gringo (Default: true)", 
    metavar='true|false')
  parser.add_option("-p", "--pure-preprocessing", dest="pure_preprocessing", default=True, type="string",
    action="callback", callback= checkTrueFalseOption, help="set pure literal preprocessing true|false (Default: true)", 
    metavar='true|false')
  parser.add_option("-e", "--explicit-preds-in-consistencies", dest="explicit_preds_consistencies", default=True, type="string",
    action="callback", callback= checkTrueFalseOption, help="set using non-flat predicates explicitly in consistency check rules true|false (Default: true)", 
    metavar='true|false')
  parser.add_option("--nonflat-function-choices", dest="nonflat_function_choices", default=True, type="string",
    action="callback", callback= checkTrueFalseOption, help="set using choice rules to interpret non-flat functions true|false. \
When it is false, deterministic interpretation of non-flat functions using interpretations of their arguments is used (Default: true)", 
    metavar='true|false')
  parser.add_option("--use-assigned-only", dest="assigned_only", default=True, type="string",
    action="callback", callback= checkTrueFalseOption, help="Effective only when nonflat-function-choices flag set to false. \
set using only assigned literal in clause and consistency constraints for equalities true|false. \
When it is false, there can be assign and assigned mixed according to the flatness of the term. (Default: true)", 
    metavar='true|false')
  parser.add_option("--dummy-assign", dest="dummy_assign", default=True, type="string",
    action="callback", callback= checkTrueFalseOption, help="set using dummy assign or assigned extensions in the base part for optimizing the grounders body literal ordering true|false. \
(Default: true)", 
    metavar='true|false')
  parser.add_option("--sort-inference", dest="sort_inference", default=True, type="string",
    action="callback", callback= checkTrueFalseOption, help="set using sort inference true|false. Sorts information will be used in symmetry breaking and grounding. \
(Default: true)", 
    metavar='true|false')
  parser.add_option("-r", "--run-iclingo", dest="run_iclingo", default=False, type="string",
    action="callback", callback= checkTrueFalseOption, help="set running iClingo internally true|false. When it is false the resulting logic program is outputted.  (Default: False)", 
    metavar='true|false')
  parser.add_option("--iclingo-bin", dest="iclingo_bin", type="string", action="store",
    default='iclingo-banane', metavar='iclingo-bin-path',
    help='set the path for iClingo executable. Default assumes that the executable is in your path (Default: iclingo-banane)')
  parser.add_option("--iclingo-opts", dest="iclingo_opts", type="string", action="store",
    default='', metavar='"iclingo-options"',
    help='set the options to use for calling iClingo. (Default: "")')
  parser.add_option("--ghostfunc-sorts", dest="ghostfunc_sorts", default=True, type="string",
    action="callback", callback= checkTrueFalseOption, help="set using a ghost function result slot while doing sort inference for deskolemized inputs true|false. *EXPERIMENTAL* Making this false cause the system become unsound. (Default: True)", 
    metavar='true|false')
  parser.add_option("--asp-based-sort-inf", dest="asp_based_sorts", default=False, type="string",
    action="callback", callback= checkTrueFalseOption, help="set infering sorts by an ASP program run by iClingo in preprocessing true|false. When it is false sorts are infered by union-find algorithm.  (Default: False)", 
    metavar='true|false')
  parser.add_option("--old-iclingo-bin", dest="old_iclingo_bin", type="string", action="store",
    default='iclingo-3.0.2', metavar='old-iclingo-bin-path',
    help='set the path for old iClingo executable (used for preprocessing). Default assumes that the executable is in your path (Default: iclingo-3.0.2)')
  parser.add_option("--has-conjecture", dest="has_conjecture", default=False, type="string",
    action="callback", callback= checkTrueFalseOption, help="set whether the original theory has conjecture or not. (Default: False)", 
    metavar='true|false')
  parser.add_option("--gzip-temp-file", dest="gzip_temp_file", default=True, type="string",
    action="callback", callback= checkTrueFalseOption, help="set whether compressed temporary file for preprocessing true|false. (Default: True)", 
    metavar='true|false')
    
  (options,args) = parser.parse_args()
  
  #print options
  #print args
  sys.stdout.write('%% iclingo\t\t: %s\n' %(options.iclingo_bin))
  sys.stdout.write('%% iclingo-opts\t\t: %s\n' %(options.iclingo_opts))
  sys.stdout.write('\n')
  
  if len(args) == 0 :
    input = sys.stdin
  else:
    input = open(args[0])
  
  try:
    root = ElementTree.parse(input)
    if not root.getroot():
      # empty input, probably eprover found an syntax error. propagate an error.
      raise Exception('Empty xml. Check for errors in previous calls to eprover, TPTP2XML, ...')
  except:
    output.write('ERROR PROPAGATION IN OUTPUT\n')
    raise
  
  global ICLINGO_BIN
  global OLD_ICLINGO_BIN
  global has_conjecture
  ICLINGO_BIN = options.iclingo_bin
  OLD_ICLINGO_BIN = options.old_iclingo_bin
  has_conjecture = options.has_conjecture
  
  if options.run_iclingo:
    #global output
    global iclingo_main_process
    iclingo_main_process = subprocess.Popen([ICLINGO_BIN]+shlex.split(options.iclingo_opts), stdin=subprocess.PIPE, stderr=subprocess.PIPE, stdout=subprocess.PIPE)
    output = iclingo_main_process.stdin
  
  if options.pure_preprocessing or options.sort_inference:
    global prepro_file
    #prepro_file = tempfile.NamedTemporaryFile(delete=False,suffix='.lp')
    if options.gzip_temp_file:
      prepro_file = gzip.open('/tmp/fimo-%s-%d.lp.gz'%(socket.gethostname(),os.getpid()), 'w+b',3)
    else:
      prepro_file = open('/tmp/fimo-%s-%d.lp'%(socket.gethostname(),os.getpid()), 'w+b')
  
  outputAllClausesPre()
  
  for elem in root.findall('formula'):
    parseFormulaXML(elem,dict())
  
  outputOccursAsComment()
  
  outputAllFunctionsPre()
  outputAllFunctions()
    
  if options.explicit_preds_consistencies:
    outputAllPredicatesPreSpecific()
  else:
    outputAllPredicatesPre()
  outputAllPredicates()
  
  outputIndependentPart()
  if options.pure_preprocessing or options.sort_inference:
    outputPreprocessingResults()
  
  outputAllConstantsPre()
  outputAllConstants()
  
  if options.sort_inference:
    outputAuxSortMax()
    
  #outputInputPredicatesFunctions()
  
  if options.run_iclingo:
    processOutputAS()
  
  #print functional_terms
  #print constants
  #print predicates,'\n'
  #print neg_predicates
  #print base_functions
  #print base_predicates
  #print base_neg_predicates, '\n'
  #print base_pos_predicates, '\n'
  
  if prepro_file:
    os.remove(os.path.abspath(prepro_file.name))
  


if __name__ == "__main__":
  main()
    
