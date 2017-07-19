#include<incmode>.

#program base.


goal(P, P):-P=1..15.
goal(16, 0).


pos(1..16).
value(0..15).

direction(up).
direction(down).
direction(left).
direction(right).

to(left, X, Y):- pos(X), Y=X-1, X!=1, X!=5, X!=9, X!=13.
to(right, X, Y):- pos(X), Y=X+1, X!=4, X!=8, X!=12, X!=16.
to(up, X, Y):- pos(X), Y=X-4, X!=1, X!=2, X!=3, X!=4.
to(down, X, Y):- pos(X), Y=X+4, X!=13, X!=14, X!=15, X!=16.


cell(P, V, 0):- init(P, V).


#program step(t).


curr(P,t-1):-cell(P,0,t-1).

%generate
1{move(D, P, t):direction(D)}1:-curr(P,t-1).

%def
:- move(D, P, t), not to(D, P, _).

%frame invariant
cell(P, V, t):- cell(P, V, t-1), not curr(P,t-1).
cell(P2, 0, t):- move(D, P, t),to(D, P, P2).
cell(P, V, t):- move(D, P, t),to(D, P, P2), cell(P2, V, t-1).

#program check(t).
#external query(t).
:-query(t), goal(P, V), not cell(P, V, t).
#show move/3.
