%hanoi tower case study!
peg(a;b;c).
disk(1..4).
init(1..4,a).
goal(1..4,c).
times(1..n).
moves(n).

%Generate
1{move(D,P,T):disk(D),peg(P)}1:-times(T).

%define
%initial
on(D,P,0):-init(D,P).

%transition
on(D,P,T):-move(D,P,T).
on(D,P,T):-on(D,P,T-1),not move(D,_,T),not moves(T-1).

%blocked : (D,P,T) D is blocked by smaller XXX in peg P on time T
%on-->blocked-->move

blocked(D-1,P,T):-on(D,P,T-1),not moves(T-1).
blocked(D-1,P,T):-blocked(D,P,T).

%restriction
%%cannot move from other places to P
:-move(D,P,T),blocked(D-1,P,T).
%%cannot move from P to another peg
:-move(D,_,T),on(D,P,T-1),blocked(D,P,T).

:-goal(D,P),not on(D,P,n).

#show move/3.





