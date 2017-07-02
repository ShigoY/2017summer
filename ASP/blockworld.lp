#include <incmode>.

%sussman Anomaly

block(b0).
block(b1).
block(b2).
block(b3).
%
%initial state:
%
%2 3
%0 1
%---------
%

init(on(b1,table)).
init(on(b2,b0)).
init(on(b0,table)).
init(on(b3,b1)).

%
%goal state:
% 3
% 2
% 1
% 0
%-------
%

goal(on(b1,b0)).
goal(on(b2,b1)).
goal(on(b0,table)).
goal(on(b3,b2)).

#program base.

%define
location(table).
location(X):-block(X).
holds(F,0):-init(F).

#program step(t).
%generate
1{move(X,Y,t):block(X),location(Y),X!=Y}1.

%Test
:-holds(on(X,Y),t-1),move(Y,_,t).
:-move(X,Y,t),holds(on(K,Y),t-1),K!=X,Y!=table.

%transition
holds(on(X,Y),t):-move(X,Y,t),holds(on(X,_),t-1).
holds(on(X,Y),t):-holds(on(X,Y),t-1),not move(X,_,t).

#program check(t).
%test
:-query(t),not goal(F),holds(F,t).

#show move/3.