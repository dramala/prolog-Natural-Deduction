verify(InputFileName) :-
see(InputFileName),
read(Prems), read(Goal), read(Proof),
seen,
valid_proof(Prems, Goal, Proof, Proof).

%Recursive. Checks wether the row passes one of the rules
valid_proof(Prems, Goal, [X,Y|T], Bevis) :-
(premise(Prems, X) ; andint(X,Bevis) ; andel1(X,Bevis);
andel2(X,Bevis) ; orint1(X,Bevis) ; orint2(X,Bevis) ; impel(X, Bevis) ; negnegint(X, Bevis) ;
copy(X,Bevis) ; negnegel(X,Bevis) ; negel(X,Bevis) ; impint(X, Bevis) ; box(Prems,X,Bevis) ; orel(X, Bevis);
contel(X,Bevis) ; negint(X,Bevis) ; lem(X) ; mt(X, Bevis) ; pbc(X, Bevis)), valid_proof(Prems,Goal,[Y|T], Bevis).

%Last row
valid_proof(Prems, Goal, [X|[]], Bevis) :-
(premise(Prems, X); andint(X,Bevis); andel1(X, Bevis); andel2(X, Bevis); orint1(X, Bevis); orint2(X, Bevis);
impel(X, Bevis); negnegint(X,Bevis); copy(X,Bevis); negnegel(X,Bevis); negel(X,Bevis); impint(X,Bevis); orel(X,Bevis);
contel(X,Bevis); negint(X,Bevis); lem(X); mt(X, Bevis); pbc(X, Bevis)), goal(X, Goal).


goal(X,Goal) :-
  member(Goal, X).

%Premise
premise(Prems, [_,Y,premise]) :- member(Y,Prems).

%And Introduction
andint([Row, and(X, Y), andint(R1, R2)], Bevis) :-
member([R1,X,_],Bevis), member([R2,Y,_], Bevis), Row > R1, Row > R2.

%And Elimination1
andel1([_, X, andel1(R)], Bevis) :-
  member([R, and(X, _), _], Bevis).

%And Elimination2
andel2([_, X, andel2(R)], Bevis) :-
  member([R, and(_, X), _], Bevis).

%Or Introduction
orint1([_, or(X, _), orint1(R)], Bevis) :-
  member([R, X, _], Bevis).

%Or Introduction
orint2([_, or(_, X), orint2(R)], Bevis) :-
  member([R, X, _], Bevis).

%Implication Elimination
impel([_, X, impel(A, I)], Bevis) :-
  member([I, imp(Y,X), _], Bevis), member([A, Y, _], Bevis).

%Negneg Introduction
negnegint([_,neg(neg(X)),negnegint(R)], Bevis) :-
  member([R,X,_], Bevis).

%negneg Elimination
negnegel([_, X, negnegel(R)], Bevis) :-
  member([R, neg(neg(X)), _], Bevis).

%Copy
copy([_,X,copy(R)], Bevis) :-
  member([R,X,_], Bevis).

% Hit fungerar allt till data2.txt
%Negel
negel([_, cont, negel(T, F)], Bevis) :-
  member([T,X,_],Bevis), member([F,neg(X),_], Bevis).

%Hit fungerar allt till data3.txt
rightbox(Prems, [X,Y|T], R, Box) :-
  member([R,_,assumption], [X,Y|T]), append([X,Y|T],[],Box).

%Denna funktion försöker hitta Boxen som impint använt sig av och sedan kollar att det är rätt assumption
%samt att man kommer fram till Y i den hittade boxen.
impint([_,imp(X,Y),impint(R0,R1)], Bevis) :-
  findbox(Bevis,R0,Box), member([R0, X, assumption],Box), member([R1, Y, _], Box).

%Denna funktion får in hela beviset och ska försöka hitta en box som har rätt rad samt är en assumption
findbox([X,Y|T],R0,Box) :-
  findbox([Y|T], R0, Box); rightbox(_,X,R0,Box).

%Basfallet, om sista elementet i beviset är en box.
findbox([X|[]], R0, Box) :-
  rightbox(_,X,R0,Box).

%Det är en Box
box(Prems,[X,Y|T], Bevis) :-
  member([_,_,assumption],[X,Y|T]), append([X,Y|T],Bevis,Storbevis), valid_proof(Prems,_,[Y|T], Storbevis).

orel([_,X,orel(OR,R1_b1,R2_b1,R1_b2,R2_b2)], Bevis) :-
  findbox(Bevis,R1_b1,Box1), findbox(Bevis,R1_b2,Box2), member([OR,or(A_B1, A_B2),_],Bevis), member([R1_B1, A_B1, assumption], Box1),
  member([R1_B2, A_B2, assumption], Box2), member([R2_b1, X, _], Box1), member([R2_b2, X, _], Box2).

contel([_,_,contel(R)], Bevis) :-
  member([R, cont, _], Bevis).

negint([_,neg(X), negint(R1,R2)], Bevis) :-
  findbox(Bevis,R1,Box), member([R1, X, assumption], Box), member([R2, cont, _], Box).

lem([_,or(X,Y), lem]) :-
  member(X,[neg(Y)]); member(Y,[neg(X)]).

mt([_,neg(X),mt(R1,R2)], Bevis) :-
  member([R1, imp(X,U), _], Bevis), member([R2, neg(U), _], Bevis).

pbc([_,X,pbc(R1,R2)], Bevis) :-
  findbox(Bevis, R1, Box), member([R1, neg(X), assumption], Box), member([R2, cont,_], Box).
