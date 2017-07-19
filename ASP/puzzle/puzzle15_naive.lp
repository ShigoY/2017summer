#include <incmode>.

#program base.

pos(1..16).
value(0..15).

direction(up).
direction(down).
direction(left).
direction(right).

%Are those necessary?

goal(P,P):-pos(P),P!=16.
goal(16,0).

cell(P,V,0):-init(P,V).

#program step(t).
%generate
1{move(D,P,t):direction(D),pos(P)}1.
%1{cell(P,V,t):value(V)}1:-pos(P).


%def

%up

cell(X,Y,t):-cell(X,0,t-1),cell(X+4,Y,t-1),move(up,X+4,t),X>=1,X<=12.
cell(X+4,0,t):-cell(X,0,t-1),cell(X+4,Y,t-1),move(up,X+4,t),X>=1,X<=12.

%down

cell(X,Y,t):-cell(X,0,t-1),cell(X-4,Y,t-1),move(down,X-4,t),X>=5,X<=16.
cell(X-4,0,t):-cell(X,0,t-1),cell(X-4,Y,t-1),move(down,X-4,t),X>=5,X<=16.

%right

cell(X,Y,t):-cell(X,0,t-1),cell(X-1,Y,t-1),move(right,X-1,t),X!=1,X!=5,X!=9,X!=13.
cell(X-1,0,t):-cell(X,0,t-1),cell(X-1,Y,t-1),move(right,X-1,t),X!=1,X!=5,X!=9,X!=13.

%left
cell(X,Y,t):-cell(X,0,t-1),cell(X+1,Y,t-1),move(left,X+1,t),X!=4,X!=8,X!=12,X!=16.
cell(X+1,0,t):-cell(X,0,t-1),cell(X+1,Y,t-1),move(left,X+1,t),X!=4,X!=8,X!=12,X!=16.


%frame invariant
cell(X,Y,t):-cell(X,Y,t-1),not move(_,X,t).


#program check(t).
:-query(t),goal(P,Q),not cell(P,Q,t).

#show move/3.
