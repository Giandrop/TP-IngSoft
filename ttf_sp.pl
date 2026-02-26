% ttf_sp.pl - release 0.1a, June 2025

:- discontiguous ttf_sp_in/2.

:- discontiguous ttf_sp/4.

% un

% ttf_sp_in(a,n) indicates the number (n) of
% the leftmost arguments of constraint a
% that are considered input arguments. For
% example in un(A,B,C) A and B are
% considered inputs so n = 2.
%
ttf_sp_in(un,2).

ttf_sp(un,1,S,T) :- S = {} & T = {}.

ttf_sp(un,2,S,T) :- S = {} & T neq {}.

ttf_sp(un,3,S,T) :- S neq {} & T = {}.

ttf_sp(un,4,S,T) :- S neq {} & T neq {} & disj(S,T).

ttf_sp(un,5,S,T) :- S neq {} & T neq {} & subset(S,T) & S neq T.

ttf_sp(un,6,S,T) :- S neq {} & T neq {} & subset(T,S) & S neq T.

ttf_sp(un,7,S,T) :- S neq {} & T neq {} & S = T.

ttf_sp(un,8,S,T) :- 
  S neq {} & T neq {} & ndisj(S,T) & nsubset(S,T) & nsubset(T,S) & S neq T.

% inters

ttf_sp_in(inters,2).

ttf_sp(inters,1,S,T) :- S = {} & T = {}.

ttf_sp(inters,2,S,T) :- S = {} & T neq {}.

ttf_sp(inters,3,S,T) :- S neq {} & T = {}.

ttf_sp(inters,4,S,T) :- S neq {} & T neq {} & disj(S,T).

ttf_sp(inters,5,S,T) :- S neq {} & T neq {} & subset(S,T) & S neq T.

ttf_sp(inters,6,S,T) :- S neq {} & T neq {} & subset(T,S) & S neq T.

ttf_sp(inters,7,S,T) :- S neq {} & T neq {} & S = T.

ttf_sp(inters,8,S,T) :-
  S neq {} & T neq {} & ndisj(S,T) & nsubset(S,T) & nsubset(T,S) & S neq T.

% diff

ttf_sp_in(diff,2).

ttf_sp(diff,1,S,T) :- S = {} & T = {}.

ttf_sp(diff,2,S,T) :- S = {} & T neq {}.

ttf_sp(diff,3,S,T) :- S neq {} & T = {}.

ttf_sp(diff,4,S,T) :- S neq {} & T neq {} & disj(S,T).

ttf_sp(diff,5,S,T) :- S neq {} & T neq {} & subset(S,T) & S neq T.

ttf_sp(diff,6,S,T) :- S neq {} & T neq {} & subset(T,S) & S neq T.

ttf_sp(diff,7,S,T) :- S neq {} & T neq {} & S = T.

ttf_sp(diff,8,S,T) :-
  S neq {} & T neq {} & ndisj(S,T) & nsubset(S,T) & nsubset(T,S) & S neq T.

% dares

ttf_sp_in(dares,2).

ttf_sp(dares,1,_,R) :- R = {} & true.

ttf_sp(dares,2,X,R) :- R neq {} & X = {}.

ttf_sp(dares,3,X,R) :- R neq {} & dom(R,X).

ttf_sp(dares,4,X,R) :- R neq {} & X neq {} & let([D], dom(R,D), subset(X,D) & X neq D).

ttf_sp(dares,5,X,R) :- R neq {} & X neq {} & let([D], dom(R,D), disj(X,D)).

ttf_sp(dares,6,X,R) :- R neq {} & let([D], dom(R,D), ndisj(X,D) & subset(D,X)).

ttf_sp(dares,7,X,R) :-
  R neq {} & let([D], dom(R,D), ndisj(X,D) & nsubset(D,X) & nsubset(X,D)).

% oplus

ttf_sp_in(oplus,2).

ttf_sp(oplus,1,R,G) :- R = {} & G = {}.

ttf_sp(oplus,2,R,G) :- R = {} & G neq {}.

ttf_sp(oplus,3,R,G) :- R neq {} & G = {}.

ttf_sp(oplus,4,R,G) :- R neq {} & G neq {} & let([A,B],dom(R,A) & dom(G,B), A = B).

ttf_sp(oplus,5,R,G) :-
  R neq {} & G neq {} & let([A,B],dom(R,A) & dom(G,B), subset(B,A) & A neq B).

ttf_sp(oplus,6,R,G) :-
  R neq {} & G neq {} & let([A,B],dom(R,A) & dom(G,B), disj(B,A)).

ttf_sp(oplus,7,R,G) :-
  R neq {} & G neq {} & let([A,B], dom(R,A) & dom(G,B), subset(A,B) & A neq B).

ttf_sp(oplus,8,R,G) :-
  R neq {} & G neq {} & 
  let([A,B], dom(R,A) & dom(G,B), ndisj(A,B) & nsubset(B,A) & nsubset(A,B)).

% rres

% (1) must be a {log} formula; otherwise unification
%     succeeds binding R to {} for the rest of the
%     computation
%
ttf_sp_in(rres,2).

ttf_sp(rres,1,R,_) :- R = {} & true.         % (1)

ttf_sp(rres,2,R,S) :- R neq {} & S = {}.

ttf_sp(rres,3,R,S) :- R neq {} & ran(R,S).

ttf_sp(rres,4,R,S) :- R neq {} & S neq {} & let([B], ran(R,B), subset(S,B) & S neq B).

ttf_sp(rres,5,R,S) :- R neq {} & S neq {} & let([B], ran(R,B), disj(S,B)).

ttf_sp(rres,6,R,S) :- R neq {} & let([B], ran(R,B), ndisj(S,B) & subset(B,S) & B neq S).
  
ttf_sp(rres,7,R,S) :-
  R neq {} & let([B], ran(R,B), ndisj(S,B) & nsubset(B,S) & nsubset(S,B)).
  
% dres

ttf_sp_in(dres,2).

ttf_sp(dres,1,_,R) :- R = {} & true.

ttf_sp(dres,2,S,R) :- R neq {} & S = {}.

ttf_sp(dres,3,S,R) :- R neq {} & dom(R,S).

ttf_sp(dres,4,S,R) :- R neq {} & S neq {} & let([A], dom(R,A), subset(S,A) & S neq A).

ttf_sp(dres,5,S,R) :- R neq {} & S neq {} & let([A], dom(R,A), disj(S,A)).

ttf_sp(dres,6,S,R) :- R neq {} & let([A], dom(R,A), ndisj(S,A) & subset(A,S) & A neq S).

ttf_sp(dres,7,S,R) :-
  R neq {} & let([A], dom(R,A), ndisj(S,A) & nsubset(A,S) & nsubset(S,A)).

% rares

ttf_sp_in(rares,2).

ttf_sp(rares,1,R,_) :- R = {} & true.

ttf_sp(rares,2,R,S) :- R neq {} & S = {}.

ttf_sp(rares,3,R,S) :- R neq {} & ran(R,S).

ttf_sp(rares,4,R,S) :- R neq {} & S neq {} & let([B], ran(R,B), subset(S,B) & S neq B).

ttf_sp(rares,5,R,S) :- R neq {} & S neq {} & let([B], ran(R,B), disj(S,B)).

ttf_sp(rares,6,R,S) :- R neq {} & let([B], ran(R,B), ndisj(S,B) & subset(B,S) & B neq S).
  
ttf_sp(rares,7,R,S) :-
  R neq {} & let([B],ran(R,B), ndisj(S,B) & nsubset(B,S) & nsubset(S,B)).
  
% rimg

ttf_sp_in(rimg,2).

ttf_sp(rimg,1,R,_) :- R = {} & true.

ttf_sp(rimg,2,R,S) :- R neq {} & S = {}.

ttf_sp(rimg,3,R,S) :- R neq {} & dom(R,S).

ttf_sp(rimg,4,R,S) :- R neq {} & S neq {} & let([A], dom(R,A), subset(S,A) & S neq A).

ttf_sp(rimg,5,R,S) :- R neq {} & S neq {} & let([A], dom(R,A), disj(S,A)).

ttf_sp(rimg,6,R,S) :- R neq {} & let([A], dom(R,A), ndisj(S,A) & subset(A,S) & A neq S).

ttf_sp(rimg,7,R,S) :-
  R neq {} & let([A], dom(R,A), ndisj(S,A) & nsubset(A,S) & nsubset(S,A)).


