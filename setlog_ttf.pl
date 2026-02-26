% setlog_ttf-0.1.5c

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                             %
%                                                             %
%                   Implementation of the                     %
%                                                             %
%               Test Template Framework for the               %
%                                                             %
%                {log} specification language                 %
%                                                             %
%        by Maximiliano Cristia' and  Gianfranco Rossi        %
%                                                             %
%                          March 2025                         %
%                                                             %
%                  Revised November 2025                      %
%                                                             %
%                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% TTF can only be called:
%  * on {log} **typechecked** state machines
%  * the state machine must have at least one invariant and one operation
%  * after the *-vc.* file has been consulted
%  * ideally once all verification conditions have been discharged
%    (not checked)

% tt means testing tree
% a tt is a tree implemented as a graph as in library(ugraphs)
% each vertex in tt is of the form [label,predicate] where
%   * label is an atom such as op_vis, op^dnf_1, op^sp_3
%   * predicate is a conjuntion of {log} atomic predicates
%     depending only on parameters, (before) state variables and
%     input variables (these are explained below)

% ts means test specification; a test specification is a predicate of a tt

% tc means test case; a test case is a conjunction of the form var = term
% where var is a variable and term is a ground term

% the following user predicates are available
%   * ttf(++spec)
%       spec is the name of the specification (an atom); the name must concide
%       with the base name of the file
%       all the remaining predicates can be executed once this one has been called
%   * applydnf(+operation) (disjunctive normal form)
%       operation is a term of the form head(I_1,...,I_n) with 0 =< n
%       head must be the name of an operation
%       I_i must be an argument to head in the state machine specification
%       I_i can't be a state variable nor a parameter
%       I_i is intended to be the an input argument to head
%       departing from the empty tt, it generates a tt such that each
%       predicate in tt is of the form
%                     axioms & precondition
%       where
%         + axioms is the conjuntion of all axioms depending on parameters appearing in
%           precondition
%         + precondition is the precondition of one conjunct of operation
%   * applysp(++label,+atom) (standard partition)
%       label is a label in the current tt
%       the current tt results from a previous call to some tactic
%       atom is a term representing an atomic predicate appearing in the
%       operation (RQ are considered atomic); variable names used in atom must coincide
%       with those used in the operation and there must be at least one IS variable; if
%       no variable in IS appears in atom the it will match with an atom with no
%       variable in IS and by using unification 
%       modifies the current tt by applying standard partition on atom to all
%         vertices of the subtree of the current tt whose root is label
%   * applyst(++label,+var) (sum type)
%       label is a label in the current tt
%       var is an input variable of a sum type
%       the current tt results from a previous call to some tactic
%       partitions all vertices of the subtree of the current tt whose root is label
%       with ts of the form var = c where c is a constructor of the sum type
%       c can have arguments
%   * applyii(++label,+var,++list) (integer interval)
%       label is a label in the current tt
%       var is an input variable of type int
%       list is a list of integer numbers
%       the current tt results from a previous call to some tactic
%       applyii sorts list
%       partitions all vertices of the subtree of the current tt whose root is label
%       with ts of the form var < i, var = i, i < var < j where i and j are in list
%   * applysc(++label,+var) (set cardinality)
%       label is a label in the current tt
%       var is an input variable of some set type
%       the current tt results from a previous call to some tactic
%       partitions all vertices of the subtree of the current tt whose root is label
%       with ts of the form:
%       V = {}, V = {X} & dec(X,T), V = {X,Y/W} & X neq Y & dec([X,Y],T) & dec(W,set(T))
%   * applyex(++label,+ex) (set cardinality)
%       label is a label in the current tt
%       ex is an exists/2 predicate where the quantification domain is either an
%       input variable or its tail is an input variable, of some set type
%       the current tt results from a previous call to some tactic
%       partitions all vertices of the subtree of the current tt whose root is label
%       with ts of the form:
%       V = {X} & dec(X,T), V = {X,Y/W} & X neq Y & dec([X,Y],T) & dec(W,set(T)),
%       V = {NegX,Y/W} & NegX neq Y & NegPred & dec([NegX,Y],T) & dec(W,set(T))
%       where NegPred is the result of negating the predicate of ex instantiated
%       at NegX.
%   * prunett(++timeout,++exec_opt)
%       the current tt results from a previous call to some tactic
%       timeout is a positive natural number that will be passed as timeout to setlog/5
%       exec_opt is a list of execution options that will be passed as the fifth argument
%         to setlog/5
%       the current tt is modified by pruning unsatisfiable leaves from it
%   * prunett/0
%       as prunett/2 where timeout and exec_opt are set by this program to some
%       fixed values
%   * gentc(++timeout,++exec_opt)
%       the current tt results from a previous call to some tactic
%       timeout is a positive natural number that will be passed as timeout to setlog/5
%       exec_opt is a list of execution options that will be passed as the fifth argument
%         to setlog/5; nogrounsol isn't accepted as an option; groundsol is added to
%         exec_op if not present
%       the current tt is modified by adding test cases to the satisfiable
%         leaves and adding a special vertex "timeout" to those leaves where the
%         call to setlog/5 finished in timeout
%   * gentc/0
%       as gentc/2 where timeout and exec_opt are set by this program to some
%       fixed values
%   * writett/0
%       the current tt results from a previous call to some tactic or gentc
%       writes the labels the current tt's nodes using indentation
%   * writetc(++label)
%       the current tt iresults from a previous call to gentc
%       label must be the label of a test case in the current tt
%       writes the corresponding test case
%   * writetc/0
%       the current tt results from a previous call to gentc
%       writes all the test cases of the current tt
%   * exporttt/0
%       the current tt results from a previous call to some tactic or gentc
%       saves test specifications in a file named spec-tt.pl 
%       (where spec is the value passed to ttf/1)
%       spec-tt.pl is a list of clauses of the form
%         label(V_1,...,V_n) :- predicate.
%       where * label is a label of a leaf ts or a tc in the current tt 
%             * V_i are the variables appearing in predicate
%             * predicate is the conjunction of all the predicates of the
%               nodes of the path from root to the leaf ts, or the tc
%       so clauses represent either leaf ts' or tc's
%
% in this way a typical use of TTF is as follows:
%   ttf(spec) -> applydnf(op) -> applysp(l,a) -> ... -> applysp(l,a) ->
%   gentc, and then one can either write or export the current tt or its test
%   specifications and test cases


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% TODO consider let !!!!
%
% TODO improve variable names of fresh variables (e.g. variables created by applysc)
%
% TODO new tactic: given a relation R, partition with:
%                npfun(R) or pfun(R) & ran(R,{X}) or 
%                pfun(R) & ninj(R) & subset({X,Y},ran(R)) & X neq Y or inj(R)
%      is it necessary distinguish the second and thir cases given that one can apply
%      set cardinality? would it be OK to combine ran with size?
%
% TODO new tactic: given a set of integers A, partition with:
%                foreach(X in A, X < 0) or foreach(X in A, X >= 0) or 
%                un(A1,A2,A) & foreach(X in A1, X < 0) & foreach(X in A2, X >= 0)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- consult('ttf_sp.pl').

ttf(Spec) :-
%  nb_setval(groundsol,off),
  (atom(Spec) ->
     (setlog:dvariables(_) ->
        nb_setval(spec,Spec),
        nb_setval(ttf_tt,[])
     ;
        error(['(ttf) no specification has been loaded'])
     )
  ;
     error(["(ttf) argument must be a Prolog atom"])
  ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% disjunctive normal form
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% TT = [[is,os,root,unfbody],tt] where
% is and os are variable names as in read_term; used to print
% output for the user
% is input variables; os output variables
% root is saved when dnf is applied to simplify some searches
% unfbody is the unfolded body of the operation being tested
% tt is the actual testing tree; root belongs to tt
%
applydnf(Op) :-
  (nb_current(ttf_tt,_) ->
     Op =.. [H | P],
     b_getval(varnames,VN),
     term_string(Op,SOp,[variable_names(VN)]),
     (is_set(P) ->
        (term_variables(P,P) ->
           ((setlog:all_unsat_vc(_,_,_,_,Op1,VN1),Op1 =.. [H | P1]) ->
              (subset(VN,VN1) ->
                 setlog:dvariables(SVN),
                 (state_variable_is_present(VN,SVN) ->
                    error(['(ttf) in ',Op,' no state variable is allowed'])
                 ;
                    (setlog:dparameters(PVN),! ; PVN = []),
                    (intersection(VN,PVN,[]) ->
                       setlog:isetlog(Op1 :- Body,usr),!,
                       functor(Op1,Name,Arity),
                       nb_setval(ttf_op,Name/Arity),
                       update(VN,VN1,IV1),        % input
                       update(SVN,VN1,SV1),       % state
                       update(PVN,VN1,PV1),       % parameters
                       append(IV1,SV1,XX),append(XX,PV1,ISVN),
                       subtract(VN1,ISVN,OSVN),   % output variables
                       term_variables(OSVN,OS),
                       genttdnf(H,OS,Body,Root,DNF,TT1),
                       nb_setval(ttf_tt,[[ISVN,OSVN,Root,DNF],TT1])
                    ;
                       error(["(ttf) specification parameters aren't allowed in ",SOp])
                    )
                 )
              ;
                 length(P1,L),
                 error(["(ttf) arguments in ",SOp," must all be arguments of operation ",H,"/",L])
              )
           ;
              length(P,L),
              error(["(ttf) ",H,"/",L," must be an operation"])
           )
        ;
           error(["(ttf) arguments in ",SOp," must all be variables"])
        )
     ;
        error(["(ttf) arguments in ",SOp," must all be different"])
     )
  ;
     error(["(ttf) ttf/1 hasn't been executed"])
  ).

state_variable_is_present(VN,SVN) :-
  intersection(VN,SVN,I),
  I \== [],!.
state_variable_is_present(VN,_) :-
  member(X=_,VN),
  sub_atom(X,_,_,0,'_'),!.            %%%%% CUT ???????

genttdnf(Op,OS,Body,Root,DNF,TT) :-
  atom_concat(Op,'_vis',VIS),
  unfold(Body,UnfBody),
  dnf(UnfBody,DNF),
  maplist(preconds(OS),DNF,PreDNF1),        % PreDNF1 contains only preconditions
  exclude(==([]),PreDNF1,PreDNF),           % if disjunct contain no precond, remove it
  dnf_ts(Op,1,[VIS,true],[[VIS,true]-[]],PreDNF,TT),
  search_node(VIS,TT,Root).

% unfold(B,-U)
% B is a {log} formula possibly containing user-defined predicates
% U is the result of substituting all calls to user-defined predicates in B
% by their corresponding bodies. as a result U contains only built-in predicates
%
unfold(B1 or B2,Unf) :-
  !,
  unfold(B1,UB1),
  unfold(B2,UB2),
  ((B1 or B2) == (UB1 or UB2) ->    % nothing was unfolded, then finish
     Unf = (B1 or B2)
  ;
     unfold(UB1 or UB2,Unf)         % something was unfolded, then unfold again
  ).
unfold(B1 & B2,Unf) :-
  !,
  unfold(B1,UB1),
  unfold(B2,UB2),
  ((B1 & B2) == (UB1 & UB2) ->      % nothing was unfolded, then finish
     Unf = (B1 & B2)
  ;
     unfold(UB1 & UB2,Unf)          % something was unfolded, then unfold again
  ).
unfold(B,Body) :-
  setlog:isetlog(B :- Body,usr),!.       % B is user-defined, must be undolfed
unfold(B,B).                             % B is built-in, nothing to do


% the following predicates writes a {log} formula into DNF
% adapted from p. 36 of Fitting's first-order logic and
% automated theorem proving

conjunctive((_ & _)).

disjunctive(_ or _).

components((X & Y),X,Y).
components((X or Y),X,Y).

singlestep([Conjunction | Rest],New) :-
  member(Alpha,Conjunction),
  conjunctive(Alpha),
  components(Alpha,A1,A2),
  exclude(==(Alpha),Conjunction,Temp),   % call to remove in Fitting's
  Newcon = [A1,A2 | Temp],
  New = [Newcon | Rest].
singlestep([Conjunction | Rest],New) :-
  member(Beta,Conjunction),
  disjunctive(Beta),
  components(Beta,B1,B2),
  exclude(==(Beta),Conjunction,Temp),    % call to remove in Fitting's
  New1 = [B1 | Temp],
  New2 = [B2 | Temp],
  New = [New1,New2 | Rest].
singlestep([Conjunction | Rest],[Conjunction | Newrest]) :-
  singlestep(Rest,Newrest).

expand(Dis,Newdis) :-
  singlestep(Dis,Temp),
  expand(Temp,Newdis),!.
expand(Dis,Dis).

% dnf(X,-Y)
% X may contain & and or
% Y is a list of lists where each list represents a conjunction
% and X is equivalent to the disjunction of all the elements of Y
%
dnf(X,Y) :- expand([[X]],Y).

% end Fitting's DNF algorithm


% collects the preconditions of a 
% conjunction of atoms (given as a list)
%
preconds(OS,Conjunction,Precond) :-
  include(precondition(OS),Conjunction,Precond).

% a precondition is an Atom whose variables
% aren't in OS (output space)
%
precondition(OS,Atom) :-
  Atom =.. [H | _],
  \+member(H,[set,rel,integer]),                        % exclude sort constraints
  term_variables(Atom,Vars),
  Vars \== [],
  forall(member(X,Vars),\+setlog:member_strong(X,OS)).  % Atom is a precondition

% generates a list of test specifications from PreDNF
% PreDNF is a list of lists
% each element of PreDNF represents a conjunction of preconditions
% each test specification is of the form [label,{log}-formula]
% where label is of the form Op_dnf_<num> and
% {log}-formula is the result of list_to_conj of an element of PreDNF
%
dnf_ts(_,_,_,TT,[],TT) :- !.
dnf_ts(Op,N,[L,P],TTi,[Conj | PreDNF],TTf) :-
  atom_concat(Op,'_dnf_',XX),
  atomic_concat(XX,N,Label),
  setlog:list_to_conj(FConj,Conj),
  add_edges(TTi,[[L,P]-[Label,FConj]],TT1),
  N1 is N + 1,
  dnf_ts(Op,N1,[L,P],TT1,PreDNF,TTf).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% standard partition
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% applysp(++label,+atom)
%
% (1) now variables in Atom coincide with
%     those used in IS+OS whenever the names
%     used in IAtom coindice with those in IS+OS
%
% (2) NewIAtom is in the external representation
%     (e.g. {A} instead of {} with A). Used to print
%     errors.
%
applysp(L,IAtom) :-
  ((nb_current(ttf_tt,[[IS,OS,Root,UnfBody],TT]),
    nonvar(IS),nonvar(OS),nonvar(TT)) ->
     (search_node(L,TT,Node) ->
        b_getval(varnames,VN1),
        append(IS,OS,IO),
        update(VN1,IO,VN),
        setlog:postproc(IAtom,IAtomP),                         % (1)
        term_string(IAtomP,SAtom,[variable_names(VN1)]),       % (1)
        term_string(AtomE,SAtom,[variable_names(VN)]),         % (1)
        setlog:preproc(AtomE,Atom,_),                          % (1)
        term_string(IAtomP,NewSAtom,[variable_names(VN1)]),    % (2)
        Atom =.. [AH | P],
        (ttf_sp_in(AH,Arity) ->
           length(P,LP),
           (Arity =< LP ->
             (arguments_ok(Atom,OS) ->
                (search_atom(AH,P,Arity,UnfBody,IO,NewSAtom,[[AH,P1,UnfBody,IO]]) ->
                   NAtom =.. [AH|P1],
                   b_getval(ttf_op,H/_),
                   genttsp(H,NAtom,Node,TT,TT1),
                   nb_setval(ttf_tt,[[IS,OS,Root,UnfBody],TT1])
                ;
                   error(["(ttf) ",NewSAtom," isn't an atom in operation"])
                )
             ;
                error(["(ttf) ",NewSAtom," contains non-input variables where input variables are expected"])
             )
           ;
             error(["(ttf) ",NewSAtom," must have at least ",Arity," arguments"])
           )
        ;
           length(P,LP),
           error(["(ttf) no standard partition has been defined for ",AH,"/",LP])
        )
     ;
        error(["(ttf) ",L," isn't a label of a test specification"])
     )
  ;
     error(["(ttf) current testing tree seems to be corrupted"])
  ).


% arguments_ok(+Atom,+OS)
% arguments of Atom are ok iff no variable in the 
% first N arguments of Atom is a variable in OS,
% where N is the number of arguments indicated in
% ttf_sp.pl
%
arguments_ok(Atom,OS) :-
  Atom =.. [H | P],
  ttf_sp_in(H,N),
  length(P1,N),
  append(P1,_,P),
  term_variables(P1,Vars),
  term_variables(OS,VOut),
  forall(member(X,Vars),\+setlog:member_strong(X,VOut)).

% search_atom(AH,P,A,Body,IO,NewSAtom,[[AH,P1,Body,IO]])
% AH head of atom
% P parameters of atom
% A is a natural number such that ttf_sp_in(AH,A) in ttf_sp.pl
% Body body of the formula
% IO input and output variables
% NewSAtom string representing the input atom given by the user
% P1 arguments of the atom as found in Body
%
% TODO this implementation stops as soon as the first atom is
%      found in Body. it should collect all occurrences of
%      atom. the code looks like as if it collects all 
%      occurrences but it doesn't. to fix this: search_atom1
%      and search_atom_conj should always be recursive;
%      findall in search_atom should be modified
%
% TODO printing should be done in applysp
%
search_atom(H,P,A,Body,IO,IAtom,Bag) :-
  length(IP,A),
  append(IP,_,P),
  findall([H,IP,Body,IO],search_atom1(H,IP,A,Body,IO),Bag),
  length(Bag,LB),
  (LB == 0,!,fail
  ;
   LB == 1,!,true
  ;
   LB > 1,
   error(["(ttf) too many matches for ",IAtom])
  ).

search_atom1(H,P,A,[Conj | _],IO) :-
   search_atom_conj(H,P,A,Conj,IO),!.
search_atom1(H,P,A,[_ | UnfBody],IO) :- search_atom1(H,P,A,UnfBody,IO).


% exact match
search_atom_conj(H,P,A,[C | _],_) :-
  C =.. [H | PC],
  length(IPC,A),
  append(IPC,_,PC),
  P == IPC,!.
% match modulo unification
search_atom_conj(H,P,A,[C | _],IO) :-
  C =.. [H | PC],
  length(IPC,A),
  append(IPC,_,PC),
  match_general(IO,P,IPC),!.
search_atom_conj(H,P,A,[_ | Rest],IO) :- search_atom_conj(H,P,A,Rest,IO).

% match modulo unification except when
% both are IO variables.
%
match_general(_,[],[]) :- !.
match_general(IO,[X|P],[Y|IPC]) :-
   var(X),var(Y),!,
   match_general_vars(IO,[X|P],[Y|IPC]).
% if X or Y are general terms, their variables must verify
% any of the above conditions
match_general(IO,[X|P],[Y|IPC]) :-
   term_variables(X,VX),
   term_variables(Y,VY),
   match_general(IO,VX,VY),
   match_general(IO,P,IPC).

% if X is an IO variable, X and Y must be the same variable
match_general_vars(IO,[X|P],[Y|IPC]) :-
   setlog:get_var(IO,X,_),!,  
   X == Y,
   match_general(IO,P,IPC).
% if Y is an IO variable, X and Y must be the same variable
match_general_vars(IO,[X|P],[Y|IPC]) :-
   setlog:get_var(IO,Y,_),!,  
   X == Y,
   match_general(IO,P,IPC).
% if both X and Y aren't IO variables, then they are unified
match_general_vars(IO,[X|P],[Y|IPC]) :-
   X = Y,
   match_general(IO,P,IPC).


% genttsp(H,Atom,Node,TTi,TTf)
% test specifications coming from the application
% of the standard partitions (SP) tactic are added to
% TTi thus returning TTf.
% test specifications are those indicated in file
% ttf_sp.pl for the head symbol of Atom.
% the nodes where SP is applied are those reachable
% from Node in TTi. these nodes are those returned
% by paths/3 called from Node.
%
genttsp(H,Atom,Node,TTi,TTf) :-
  Node = [L,P],
  paths([L,P],TTi,Paths),
  maplist(conj_to_list,Paths,FPreds),
  sp_for_atom(Atom,SPS),
  update_tt(H,sp,L,P,FPreds,TTi,SPS,TTf).
  
% sp_for_atom/2
% TSS is the list of test specifications
% retrieved from file ttf_sp.pl for the
% head symbol of Atom where the last K
% arguments of the clauses in ttf_sp.pl
% are unified with the first K arguments
% of Atom.
%
sp_for_atom(Atom,TSS) :-
  Atom =.. [H | P],
  ttf_sp_in(H,K),
  length(P1,K),
  append(P1,_,P),
  sp_for_atom(H,P1,1,TSS).

% sp_for_atom/4
sp_for_atom(H,P,N,TSS) :-
  SP =.. [ttf_sp,H,N | P],
  clause(setlog:SP,Body),!,
  TSS = [Body | TSS1],
  N1 is N + 1,
  sp_for_atom(H,P,N1,TSS1).
sp_for_atom(H,P,N,[]) :-
  SP =.. [ttf_sp,H,N | P],
  \+clause(SP,_),!.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% sum types
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

applyst(L,VarN) :-
  b_getval(varnames,VN),
  (var(VarN) ->
    setlog:get_var(VN,VarN,AVarN),
    ((nb_current(ttf_tt,[[IS,OS,Root,UnfBody],TT]),
      nonvar(IS),nonvar(OS),nonvar(TT)) ->
       (member(AVarN = Var,IS) ->
          (search_node(L,TT,Node) ->
             b_getval(sum_vars,SV),
             (member([AVarN,Type],SV),! ->
                b_getval(ttf_op,H/_),
                (Type = sum(List),! ; Type = enum(List)),
                genttst(H,Var,List,Node,TT,TT1),
                nb_setval(ttf_tt,[[IS,OS,Root,UnfBody],TT1])
             ;
                error(["(ttf) ",AVarN," is not of a sum type"])
             )
          ;
             error(["(ttf) ",L," isn't a label of a test specification"])
          )
       ;
          b_getval(ttf_op,H/Len),
          error(["(ttf) ",AVarN," is not an input variable in ",H,"/",Len])
       )       
    ;
       error(["(ttf) current testing tree seems to be corrupted"])
    )
  ;
     error(["(ttf) second argument must be a variable"])
  ).

genttst(H,Var,Type,Node,TTi,TTf) :-
  Node = [L,P],
  paths([L,P],TTi,Paths),
  maplist(conj_to_list,Paths,FPreds),
  maplist(subs_types_in_sum,Type,TSS),
  maplist(geneq(Var),TSS,Eqs),
  maplist(conj_eq_dec,Eqs,TSS,Type,SPS),
  update_tt(H,st,L,P,FPreds,TTi,SPS,TTf).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% integer intervals
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% TODO extend to Expr instead of VarN
%
applyii(L,VarN,List) :-
  b_getval(varnames,VN),
  (var(VarN) ->
    setlog:get_var(VN,VarN,AVarN),
    b_getval(typed_vars,TV),
    b_getval(ttf_op,Op),
    (member([Op,AVarN,int],TV) ->
       ((nb_current(ttf_tt,[[IS,OS,Root,UnfBody],TT]),
         nonvar(IS),nonvar(OS),nonvar(TT)) ->
          (member(AVarN = Var,IS) ->
             (search_node(L,TT,Node) ->
                ((is_list(List), List \== [], forall(member(X,List),integer(X))) ->
                   sort(List,SList),
                   Op = HOp/_,
                   genttii(HOp,Var,SList,Node,TT,TT1),
                   nb_setval(ttf_tt,[[IS,OS,Root,UnfBody],TT1])
                ;
                   error(["(ttf) third argument must be a non-empty list of integers"])
                )
             ;
                error(["(ttf) ",L," isn't a label of a test specification"])
             )
          ;
             Op = HOp/Ar,
             error(["(ttf) ",AVarN," isn't an input variable in ",HOp,"/",Ar])
          )       
       ;
          error(["(ttf) current testing tree seems to be corrupted"])
       )
    ;
       Op = HOp/Ar,
       error(["(ttf) ",AVarN," isn't of type int in ",HOp,"/",Ar])
    )
  ;
     error(["(ttf) second argument must be a variable"])
  ).

genttii(H,Var,List,Node,TTi,TTf) :-
  Node = [L,P],
  paths([L,P],TTi,Paths),
  maplist(conj_to_list,Paths,FPreds),
  maplist(genineq(Var),List,List1),
  gen_ts_ii(List1,SPS),
  update_tt(H,ii,L,P,FPreds,TTi,SPS,TTf).

% [[V<2, V=2, 2<V], [V<5, V=5, 5<V], [V<8, V=8, 8<V]] -->
% [V<2, V=2, 2<V&V<5, V=5, 5<V&V<8, V=8, 8<V]
%
gen_ts_ii([L],L) :- !.
gen_ts_ii([[L11,L12,L13],[L21,L22,L23] | IL],FL) :-
  !,
  FL = [L11,L12,L13 & L21,L22 | FL1],
  gen_ts_ii([[L23] | IL],FL1).
gen_ts_ii([[L13],[L21,L22,L23] | IL],FL) :-
  FL = [L13 & L21,L22 | FL1],
  gen_ts_ii([[L23] | IL],FL1).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% set cardinality
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% ts generated for variable V of type set(T):
%   V = {}, V = {X} & dec(X,T), V = {X,Y/W} & X neq Y & dec([X,Y],T) & dec(W,set(T))
%
% TODO add an argument to receive the maximum cardinality
%
applysc(L,VarN) :-
  b_getval(varnames,VN),
  (var(VarN) -> 
    setlog:get_var(VN,VarN,AVarN),
    b_getval(typed_vars,TV),
    b_getval(ttf_op,Op),
    (member([Op,AVarN,set(Type)],TV) ->
       ((nb_current(ttf_tt,[[IS,OS,Root,UnfBody],TT]),
         nonvar(IS),nonvar(OS),nonvar(TT)) ->
          (member(AVarN = Var,IS) ->
             (search_node(L,TT,Node) ->
                Op = HOp/_,
                genttsc(HOp,Var,Type,Node,TT,TT1),
                nb_setval(ttf_tt,[[IS,OS,Root,UnfBody],TT1])
             ;
                error(["(ttf) ",L," isn't a label of a test specification"])
             )
          ;
             Op = HOp/Ar,
             error(["(ttf) ",AVarN," isn't an input variable in ",HOp,"/",Ar])
          )       
       ;
          error(["(ttf) current testing tree seems to be corrupted"])
       )
    ;
       Op = HOp/Ar,
       error(["(ttf) ",AVarN," isn't of a set type in ",HOp,"/",Ar])
    )
  ;
     error(["(ttf) second argument must be a variable"])
  ).

genttsc(H,V,T,Node,TTi,TTf) :-
  Node = [L,P],
  paths([L,P],TTi,Paths),
  maplist(conj_to_list,Paths,FPreds),
  gen_ts_sc(V,T,SPS),
  update_tt(H,sc,L,P,FPreds,TTi,SPS,TTf).

gen_ts_sc(V,T,SPS) :-
  SPS = [V = {},V = {X} & dec(X,T),V = {X,Y/W} & X neq Y & dec([X,Y],T) & dec(W,set(T))].

  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% exists
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% ts generated for exists(C in V,Pred):
%   V = {X} & dec(X,T), 
%   V = {X,Y/W} & X neq Y & dec([X,Y],T) & dec(W,set(T)),
%   V = {NegX,Y/W} & NegX neq Y & NegPred & 
%            dec([NegX,Y],T) & dec(W,set(T))
% where NegPred is the result of negating Pred
% instantiated at NegX.
%
% (1) variables in VN are unified with those in IO
%     in this way the IO variables appearing in 
%     EX now coincide with those appearing in the
%     operation
% (2) C is the exists/2 predicate that matches with
%     EX in UnfBody (i.e. the operation). we use it,
%     instead of EX, to generate the partition
%     because it contains some dec/2 that are missed
%     in EX.
%
applyex(L,EX) :-
  EX = exists(_ in Dom,_),
  % TODO is it necessary to check set(Dom) and the form of CE?
  setlog:tail(Dom,VDom),
  (var(VDom) ->
     b_getval(varnames,VN),
     term_string(EX,EXS,[variable_names(VN)]),
     setlog:get_var(VN,VDom,AVDom),
     b_getval(typed_vars,TV),
     b_getval(ttf_op,Op),
     ((nb_current(ttf_tt,[[IS,OS,Root,UnfBody],TT]),
       nonvar(IS),nonvar(OS),nonvar(TT)) ->
        (member(AVDom = Var,IS) ->
           (member([Op,AVDom,set(Type)],TV) ->
              (search_node(L,TT,Node) ->
                 append(IS,OS,IO),
                 intersection(VN,IO,_),              % (1)
                 (search_exists(EX,UnfBody,IO,EXS,[[EX,UnfBody,IO,C]]) ->
                    C = exists(CEC in _, PredC),     % (2)
                    Op = HOp/_,
                    genttex(HOp,Var,Type,CEC,PredC,Node,TT,TT1),
                    nb_setval(ttf_tt,[[IS,OS,Root,UnfBody],TT1])
                 ;
                    error(["(ttf) ",EXS," isn't an atom in operation"])
                 )
               ;
                  error(["(ttf) ",L," isn't a label of a test specification"])
              )
           ;
              Op = HOp/Ar,
              error(["(ttf) ",AVDom," isn't of a set type in ",HOp,"/",Ar])
           )
        ;
           Op = HOp/Ar,
           error(["(ttf) ",AVDom," isn't an input variable in ",HOp,"/",Ar])
        )
     ;
           error(["(ttf) current testing tree seems to be corrupted"])
     )
  ;
     error
  ).

% searches EX in Body
% since there can be more than one match
% all of them are collected but the
% predicate succeeds only when there's
% exactly one match.
%
search_exists(EX,Body,IO,EXS,Bag) :-
  findall([EX,Body,IO,C],search_exists1(EX,Body,IO,C),Bag),
  length(Bag,LB),
  (LB == 0,!,fail
  ;
   LB == 1,!,true
  ;
   LB > 1,
   error(["(ttf) too many matches for ",EXS])
  ).

search_exists1(EX,[Conj | _],IO,C) :-
   search_exists_conj(EX,Conj,IO,C),!.
search_exists1(EX,[_ | Body],IO,C) :- search_exists1(EX,Body,IO,C).

% EX matches with C if they unify but after
% variables in IO have been substituted
% by their names. in this way:
%   exists(X in 'S', X > 0) and
%   exists(X in 'T', X > 0)
% don't match because they can't unify
% due to 'S' and 'T'.
%
% (1) it doesn't seem to work if L1 is
%     written in the last maplist, i.e.:
%       maplist(subs_name(IS),VC,L1)
%
search_exists_conj(EX,[C | _],IO,C) :-
  C =.. [exists,_ in _,_],
  setlog:remove_dec(C,C1),
  term_variables(EX,VEX),
  term_variables(C1,VC),
  maplist(subs_name(IO),VEX,L1),
  maplist(subs_name(IO),VC,L2),
  L1 = L2,                         % (1)
  EX = C1,!.
search_exists_conj(EXS,[_ | Rest],IO,C) :- search_exists_conj(EXS,Rest,IO,C).

% just to be used by maplist
% returns the name (N) of
% variable (V) according to VN.
% if V isn't in VN then V itself is
% returned
%
subs_name(VN,V,N) :-  (setlog:get_var(VN,V,N),! ; V=N).

genttex(H,V,T,CE,Pred,Node,TTi,TTf) :-
  Node = [L,P],
  paths([L,P],TTi,Paths),
  maplist(conj_to_list,Paths,FPreds),
  gen_ts_ex(V,T,CE,Pred,SPS),
  update_tt(H,ex,L,P,FPreds,TTi,SPS,TTf).

% the idea is that NegX should be an element of V not satisfying Pred
% the elements of V are of the form CE (CE is the control expression
% of a REQ with domain V)
%
gen_ts_ex(V,T,CE,Pred,SPS) :-
  setlog:ctrl_expr(CE,[],LV,NegX),
  setlog:chvar(LV,[],_FVars,[Pred,CE,true,CE],[],_FVarsNew,[PredNew,_PNew,true,NegX]),
  setlog:negate(PredNew,NegPred),
  term_variables(NegX,VNegX),
  maplist(get_type_from_term_map(NegX,T),VNegX,TVNegX),
  maplist(dec_pred,VNegX,TVNegX,NegXDEC_L),
  setlog:list_to_conj(NegXDEC,NegXDEC_L),
  SPS = [V = {X} & dec(X,T),
         V = {X,Y/W} & X neq Y & dec([X,Y],T) & dec(W,set(T)),
         V = {NegX,Y/W} & NegX neq Y & NegPred & NegXDEC & dec(Y,T) & dec(W,set(T))].

get_type_from_term_map(Term,Type,X,Tx) :- setlog:get_type_from_term(X,Term,Type,Tx).

  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% prune
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% TODO check what options cannot be passed
%
% (1) test cases are removed to allow for several
%     calls to prunett even after gentc has been
%     called. then, it only attempts to prune those
%     leaves that aren't test cases.
%
prunett(Timeout,Opt) :-
  ((nb_current(ttf_tt,[[IS,OS,Root,UB],TT]),nonvar(Root),nonvar(TT)) ->
     ((\+member(groundsol,Opt),\+member(type_check,Opt)) ->
        paths(Root,TT,Paths),
        exclude(test_case,Paths,Paths1),           % (1)
        (Paths1 == [] ->
           format("ttf: nothing to do~n")
        ;      
           maplist(conj_to_list,Paths1,FPreds),
           write_progress_p,
           prune_leaves(Timeout,Opt,TT,FPreds,TT1),
           write_progress_e,
           nb_setval(ttf_tt,[[IS,OS,Root,UB],TT1])
        )
     ;
        error(["(ttf) groundsol and type_check are not allowed here"])
     )
  ;
     error(["(ttf) current testing tree seems to be corrupted"])
  ).

% TODO get timeout and options from the environment
%
prunett :- prunett(60000,[]).

prunett(Opt) :- prunett(60000,Opt).

% TODO improve timeout management
%
prune_leaves(_,_,TT,[],TT) :- !.
prune_leaves(Timeout,Opt,TTi,[[PathP,[L,P]] | Paths],TTf) :-
  copy_term(PathP,PathP1),
  write_progress_i(prune,L),
  setlog:rsetlog(PathP1,Timeout,_,Res,Opt),!,
  write_progress_f,
  (Res == failure ->
     del_vertices(TTi,[[L,P]],TT1)
  ;
     (Res == time_out ->
        TT1 = TTi,
        format("ttf: {log} timed out at ~s~n",L)
     ;
        TT1 = TTi
     )
  ),
  prune_leaves(Timeout,Opt,TT1,Paths,TTf) .
  

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% test case generation
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% gentc(++timeout,++exec_opt)
% adds test cases to the current tt
% timeout and exec_opt are passed to setlog
% test case generation is performed by {log}
% the formulas passed in to setlog are the conjunction
% of the predicates of each node in a path from the
% root node to one leaf. then, there's one formula
% for each path from root to a leaf.
% {log} may return a test case, a failure or timeout
% if a tc is returned it's added to TTi as a child of
% the leaf node of the corresponding path
% if timeout or failure is returned a message is printed 
%
% (1) test cases are removed to allow for several
%     calls to gentc. then, from the second call on
%     it only attempts to find test cases for those
%     test specifications for which none was
%     already found.
%
gentc(Timeout,Opt) :-
  ((nb_current(ttf_tt,[[IS,OS,Root,UB],TT]),nonvar(IS),nonvar(Root),nonvar(TT)) ->
      (\+member(groundsol,Opt) -> Opt1 = [groundsol | Opt] ; Opt1=Opt),
      paths(Root,TT,Paths),
      exclude(test_case,Paths,Paths1),       % (1)
      (Paths1 == [] ->
         format("ttf: nothing to do~n")
      ;
         maplist(conj_to_list,Paths1,FPreds),
         write_progress_p,
         generate_tc_set(FPreds,IS,Timeout,Opt1,TCS),
         process_tc_set(TCS,TT,TT1),!,
         write_progress_e,
         nb_setval(ttf_tt,[[IS,OS,Root,UB],TT1])
      ),
      nb_setval(groundsol,off),
      nb_setval(type_check,off)
  ;
      error(["(ttf) current testing tree seems to be corrupted"])
  ).

% TODO get timeout and options from the environment
%
gentc :-
  gentc(60000,[type_check,groundsol]),
  nb_setval(groundsol,off),
  nb_setval(type_check,off).

% TSS -> test specification set
% each test specification
% is a pair [PP,[L,P]] where 
% PP is the path of the second component of each node
% (i.e. predicates); and [L,P] is the leaf node. these
% tuples are taken from the paths from root to each leaf
% setlog_str with groundsol activated is called for each
% PP. the result of these calls are put in TCS; each
% result is a 4-tuple [R,L,P,TC] where R is the value of
% the fifth argument of setlog_str; [L,P] are those of the
% corresponding pair in TSS; and TC (test case) is,
% when R = success, a list of elements of the form N = V
% where N is a variable name (as in read_term) and V is a
% ground term; when R in {failure,timeout} V is a variable
%
% (1) in F types aren't expanded while in TV they are
%     so expand_types replaces dec(V,T) by dec(V,ET)
%     where ET is the expansion of T
%
generate_tc_set([],_,_,_,[]) :- !.
generate_tc_set([[F,[L,P]] | TSS],IS,T,Opt,[[Res,L,P,TC1] | TCS1]) :-
  term_variables(F,VarF),
  restrict(VarF,IS,TC),
  b_getval(typed_vars,TV),
  b_getval(ttf_op,Op),
  include(first(Op),TV,TVOp),
  gen_dec_tc(TC,TVOp,DEC),
  setlog:list_to_conj(F,FL),
  expand_types(FL,FL1),          % (1)
  setlog:list_to_conj(F2,FL1),
  copy_term([TC,(F2 & DEC)],[TC1,F1]),
  term_string(F1,SF,[variable_names(TC1)]),
  write_progress_i(gentc,L),
  (setlog:setlog_str(SF,TC1,T,_,Res,Opt),! ; Res = failure),
  write_progress_f,
  generate_tc_set(TSS,IS,T,Opt,TCS1).

process_tc_set([],TT,TT) :- !.
process_tc_set([[R,L,P,TC] | TCS],TTi,TTf) :-
  process_tc([R,L,P,TC],TTi,TT1),
  process_tc_set(TCS,TT1,TTf).

process_tc([success,L,P,TC],TTi,TTf) :-
  atomic_list_concat(LL,'_',L),
  append(OpL,[_,N],LL),!,                  
  atomic_list_concat(OpL,'_',Op),
  %atomic_list_concat([Op,_,N],'_',L),
  atom_concat(Op,'_tc_',XX),
  atom_concat(XX,N,L1),
  add_edges(TTi,[[L,P]-[L1,TC]],TTf).
process_tc([time_out,L,_,_],TT,TT) :-
  format("ttf: {log} timed out at ~s~n",L).
process_tc([failure,L,_,_],TT,TT) :-
  format("ttf: ~s should be pruned, call prunett~n",L).

% generates a conjunction of dec predicates for
% each variable in TC according to the declaration
% in TVOp
%
gen_dec_tc([],_,true) :- !.
gen_dec_tc([Name=Var | TC],TV,(dec(Var,Type) & DEC)) :-
  member([_,Name,Type],TV),!,
  gen_dec_tc(TC,TV,DEC).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% writett, writetc, exporttt
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

tab("  ").

writett :-
  ((nb_current(ttf_tt,[[_,_,Root,_],TT]),nonvar(Root),nonvar(TT)) ->
     Root = [L,_],
     nl,write(L),
     neighbors(Root,TT,Nei),
     tab(Tab),
     write_children(TT,Tab,"",Nei),
     nl
  ;
     error(["(ttf) current testing tree seems to be corrupted"])
  ).

write_children(_,_,_,[]) :- !.
write_children(TT,Tab,ITab,[[L,P] | Nei]) :-
  string_concat(ITab,Tab,NTab),
  (sub_atom(L,_,_,_,'_tc_') ->
     write(' -> '),ansi_format([bold,fg(green)],'~w',[L])
  ;
     nl,write(NTab),write(L)
  ),
  neighbors([L,P],TT,Nei1),
  write_children(TT,Tab,NTab,Nei1),
  write_children(TT,Tab,ITab,Nei).

writetc(Label) :-
  (atom(Label) ->
     (sub_atom(Label,_,_,_,'_tc_') ->
        ((nb_current(ttf_tt,[_,TT]),nonvar(TT)) ->
           (search_node(Label,TT,[_,TC]) ->
              writetc1(Label,TC)
           ;
              error(["(ttf) ",Label," isn't a test case in the current testing tree"])
           )
        ;
           error(["(ttf) current testing tree seems to be corrupted"])
        )
     ;
        error(["(ttf) the argument must be of the form <atom>_tc_<number>"])
        
     )
  ;
     error(["(ttf) the argument must be a Prolog atom"])
  ).

writetc1(Label,TC) :-
  nl,
  ansi_format([bold,fg(green)],'~w ',[Label]),
  write('is:'),
  nl,
  setlog:write_subs_all(TC,y),nl.

writetc :-
  ((nb_current(ttf_tt,[_,TT]),nonvar(TT)) ->
     leaves(TT,Leaves),
     writetcs(Leaves)
  ;
     error(["(ttf) current testing tree seems to be corrupted"])
  ).

leaves([],[]) :- !.
leaves([Node-[] | TT],[Node | Leaves]) :- !,leaves(TT,Leaves).
leaves([_ | TT],Leaves) :- leaves(TT,Leaves).

% (1) not all leaves are tc; they can be ts
%     for which {log} was unable to find a
%     solution in the given time
%
writetcs([]) :- !.
writetcs([[Label,TC] | TCS]) :-
  (sub_atom(Label,_,_,_,'_tc_') ->   % (1)
     writetc1(Label,TC)
  ;
     true
  ),
  writetcs(TCS).

file_extension(slog).

exporttt :-
  ((nb_current(ttf_tt,[[IS,_,Root,_],TT]),nonvar(IS),nonvar(Root),nonvar(TT)) ->
    paths(Root,TT,Paths),
    maplist(varname,IS,Names),
    nb_getval(spec,Spec),
    Root = [L,_],
    atomic_list_concat(OpL1,'_',L),
    append(OpL,[vis],OpL1),!,            
    atomic_list_concat(OpL,'_',Op),
    %atomic_list_concat([Op,vis],'_',L),
    file_extension(FE),
    atomic_list_concat([Spec,'_',Op,'-tt.',FE],File),
    open(File,write,Stream),
    exporttt(Stream,Names,IS,Paths),
    close(Stream),
    format("ttf: testing tree successfully exported to ~s~n",File)
  ;
     error(["(ttf) current testing tree seems to be corrupted"])
  ).

% exporttt(Stream,IS,Paths)
%
exporttt(_,_,_,[]) :- !.
exporttt(Stream,Names,IS,[[Path,[Label,P]] | Paths]) :-
  (sub_atom(Label,_,_,_,'_tc_') ->
     atomic_list_concat(LLabel,'_',Label),
     append(OpL,[tc,Num],LLabel),!,         
     atomic_list_concat(OpL,'_',Op),
     %atomic_list_concat([Op,tc,Num],'_',Label),
     atomic_list_concat([Op,ts,Num],'_',Label1),   % substitute _tc_ by _ts_
     append(TS,[P],Path),
     export_ts(Stream,Names,Label1,IS,TS),!,       % export test specification
     export_tc(Stream,Names,Label,P)               % export test case
  ;
     export_ts(Stream,Names,Label,IS,Path),!       % no tc to export, export ts
  ),
  exporttt(Stream,Names,IS,Paths).

export_ts(Stream,Names,Label,IS,TS) :-
  write_head(Stream,Names,Label),
  append(F,[LastF],TS),!,           % last element is treated differently
  forall(member(X,F),               % F is a list of conjunctions (&)
    (setlog:list_to_conj(X,L),      % turn each element of F into a list
     forall(member(Y,L),            % L is a list of atoms
       (Y \== true ->
          setlog:postproc(Y,NewY),
          term_string(NewY,SY,[variable_names(IS)]),
          format(Stream,'  ~w &\n',[SY])      % write each atom in a new line
       ;  true
       )
     )
    )
  ),
  setlog:list_to_conj(LastF,LF),   % same as above with last element of TS
  (LF \== [] -> 
     append(F1,[LastLF],LF),!,
     forall(member(X,F1),
       (X \== true ->
          setlog:postproc(X,NewX),
          term_string(NewX,SX,[variable_names(IS)]),
          format(Stream,'  ~w &\n',[SX])
       ;
          true
       )
     ),
     setlog:postproc(LastLF,NewLastLF),
     term_string(NewLastLF,SLF,[variable_names(IS)]),
     format(Stream,'  ~w.\n\n',[SLF])
  ;
     format(Stream,'  true.\n\n',[])
  ).

export_tc(Stream,Names,Label,P) :-
  write_head(Stream,Names,Label),
  append(F,[LastF],P),!,              % P is a list of N = V; last elem. is treated diff.
  forall(member(X,F),format(Stream,'  ~w &\n',[X])),
  format(Stream,'  ~w.\n\n',[LastF]).
  
write_head(Stream,Names,Label) :-
  format(Stream,'~a(',[Label]),
  append(L,[Last],Names),!,
  forall(member(X,L),format(Stream,'~a,',[X])),
  format(Stream,'~a) :-\n',[Last]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% auxiliary
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% search_node(++L,+TT,-Node)
% returns the Node of TT with label L
%
search_node(L,[[L,P]-_ | _],[L,P]) :- !.
search_node(L,[_ | Rest],Node) :- search_node(L,Rest,Node).

% update(+R,+S,-T)
% R, S and T are variable names as in read_term
% update(R,S,T) <==> 
% T = ((\dom S) \ndres R) \cup ((\dom R) \dres S)
%
% TODO it should be done for ordered pairs,
%      instead of equalities
%
update([],_,[]) :- !.
update([X = V | R],S,T) :-
  update_single(X = V,S,B),
  T = [B | T1],
  update(R,S,T1).

update_single(X = V,[],X = V) :- !.
update_single(X = _,[X1 = V1 | _],X1 = V1) :-
  X == X1,!.
update_single(X = V,[_ = _ | R],P) :-
  update_single(X = V,R,P).

% paths(Root,TT, Paths)
%
% adapted from
% https://www.geeksforgeeks.org/given-a-binary-tree-print-all-root-to-leaf-paths/
%
% collects all the paths from Root to each leaf of TT
% a path is a pair [PP,[L,P]] where PP is the path of
% the second components of each node (i.e. predicates);
% and [L,P] is the leaf node of the path
% Root can be any node in TT
%
paths(Root,TT, Paths) :-
  collectPaths(Root,[[],_],_,[],Paths,TT).

% collectPaths(Node,Path1,Path,Paths1,Paths,TT)
% Node is the starting node of paths
% Path1 and Path compute a path that at some point
% is added to Paths1/Paths
% Path1 and Path represent two states of a path
% computation (Path1, before state; Path, after state)
% Paths1 and Paths are like Path1 and Paths but for
% the set of paths that's being collected
%
collectPaths([L,P],[Path1,_],[Path,_],Paths1,Paths,TT) :-
  append(Path1,[P],Path),                           % add current node to Path
  neighbors([L,P],TT,Nei),
  (Nei == [] ->                                     % if node is leaf
     append(Paths1,[[Path,[L,P]]],Paths)            % add Path to Paths
  ;                                                 % if node isn't leaf
     collectPaths1(Nei,[Path,_],_,Paths1,Paths,TT)  % get all the paths of its children
  ).

collectPaths1([],_,_,Paths,Paths,_) :- !.
collectPaths1([L|Nei],Path,_,Paths1,Paths,TT) :-
  collectPaths(L,Path,[Path2,_],Paths1,Paths2,TT),
  append(Path3,[_],Path2),!,                        % pop last element of Path, backtrack
  collectPaths1(Nei,[Path3,_],_,Paths2,Paths,TT).

% updates the current tt TTi with the ts in SPS
% the new tt is TTf
% H, Tag and L are used to build the label of the
% new nodes of the tt
% [L,P] is the root node
%
update_tt(H,Tag,L,P,FPreds,TTi,SPS,TTf) :-
  (FPreds == [] ->                         % Node is partitioned
     atomic_list_concat([H,'_',Tag,'_'],L1),
     atomic_list_concat([_,_,Idx],'_',L),
     atom_concat(L1,Idx,Label),
     add_ts_node(TTi,[L,P],Label,1,SPS,TTf)
  ;                                        % leaves reachable from Node are partitioned
     atomic_list_concat(['_',Tag,'_'],Tag1),
     add_ts_leaves(Tag1,TTi,H,FPreds,SPS,TTf)
  ).

% partitions the test specifications in FPreds
% these ts are the leaves reachable from a 
% certain node in the TT
% SPS is the partition (a list of predicates)
%
% (1) this goal:
%        atomic_list_concat(L,'_','move_non_ambtrain_1_dnf_1'),append(_,[Idx],L).
%     asks for more solutions but there's none
%     so is it the cut necessary?
%
add_ts_leaves(_,TT,_,[],_,TT) :- !.
add_ts_leaves(TN,TTi,Op,[[_,[L,P]] | FPreds],SPS,TTf) :-
  atom_concat(Op,TN,L1),
  atomic_list_concat(LL,'_',L),
  append(_,[Idx],LL),!,
  %atomic_list_concat([_,_,Idx],'_',L),
  atom_concat(L1,Idx,Label),
  add_ts_node(TTi,[L,P],Label,1,SPS,TT1),
  add_ts_leaves(TN,TT1,Op,FPreds,SPS,TTf).

% partitions Node
%
add_ts_node(TT,_,_,_,[],TT) :- !.
add_ts_node(TTi,Node,Label,N,[SP | SPS],TTf) :-
  atomic_concat(Label,N,L1),
  add_edges(TTi,[Node-[L1,SP]],TT1),
  N1 is N + 1,
  add_ts_node(TT1,Node,Label,N1,SPS,TTf).

% restrict(+Vars,+VN,-VNNew)
% Vars is a list of variables
% VN is variable names as in read_term
% VNNew are the elements N = V of VN such that V belongs to Vars
% it's like Z's rres; i.e. VNNew = VN \rres Vars
%
% TODO check if it can be implemented with exclude or friends
% 
restrict([],_,[]) :- !.
restrict([X|VarF],VN,[N = X|NF]) :-
  member(N = V,VN),
  X == V,!,
  restrict(VarF,VN,NF).
restrict([_|VarF],VN,NF) :-
  restrict(VarF,VN,NF).

% just to use these with maplist
%
conj_to_list([ListP,[L,P]],[F,[L,P]]) :- setlog:list_to_conj(F,ListP).

% just to be used with maplist
%
varname(X=_,X).

% just to be used with maplist
%
geneq(X,Y,X=Y).

% just to be used with maplist
%
genineq(X,Y,[X<Y,X=Y,Y<X]).

% just to be used with include
%
first(X,[X|_]).

% just to be used with maplist
%
conj_eq_dec(Eq,CV,CT,(Eq & F)) :-
  CV =.. [H|P],
  CT =.. [H|P1],
  maplist(dec_pred,P,P1,L),
  setlog:list_to_conj(F,L).

% just to be used with maplist
%
dec_pred(X,Y,dec(X,Y)).

% just to be used with maplist
%
subs_types_in_sum(C,T) :- C =.. [H|P], length(P,L), functor(T,H,L).

% just to be used with exclude
%
test_case([_,[L,_]]) :- sub_atom(L,_,_,_,'_tc_'),!.

% error/exception printing
%
error(E) :- atomic_list_concat(E,EM), throw(setlog_excpt(EM)).

% progress pretty-printing
% 
write_progress_p.
% write_progress_p :- write(' '),nl.

write_progress_e :-
  write('                                                                        ').

write_progress_i(prune,L) :-
  write('Pruning test specification: '),write(L),flush_output.
write_progress_i(gentc,L) :-
  write('Generating test case for: '),write(L),flush_output.

write_progress_f :-
  write('\r'),
  write('                                                                        '),
  write('\r'),
  flush_output.

expand_types([],[]) :- !.
expand_types([C | L],[dec(V,ET) | NL]) :-
  C = dec(V,T),!,
  setlog:expand_type(T,ET),
  expand_types(L,NL).
expand_types([C | L],[C | NL]) :- expand_types(L,NL).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% {log} commands
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

setlog_command(ttf(_)) :- !.
setlog_command(applydnf(_)) :- !.
setlog_command(applysp(_,_)) :- !.
setlog_command(applyst(_,_)) :- !.
setlog_command(applyii(_,_,_)) :- !.
setlog_command(applysc(_,_)) :- !.
setlog_command(applyex(_,_)) :- !.
setlog_command(prunett(_,_)) :- !.
setlog_command(prunett(_)) :- !.
setlog_command(prunett) :- !.
setlog_command(gentc(_,_)) :- !.
setlog_command(gentc) :- !.
setlog_command(writett) :- !.
setlog_command(writetc(_)) :- !.
setlog_command(writetc) :- !.
setlog_command(exporttt) :- !.

ssolve_command(ttf(Spec)) :- !, ttf(Spec).
ssolve_command(applydnf(Op)) :- !, applydnf(Op).
ssolve_command(applysp(Label,Atom)) :- !, applysp(Label,Atom).
ssolve_command(applyst(Label,Var)) :- !, applyst(Label,Var).
ssolve_command(applyii(Label,Var,List)) :- !, applyii(Label,Var,List).
ssolve_command(applysc(Label,Var)) :- !, applysc(Label,Var).
ssolve_command(applyex(Label,EX)) :- !, applyex(Label,EX).
ssolve_command(prunett(T,Opt)) :- !, prunett(T,Opt).
ssolve_command(prunett(Opt)) :- !, prunett(Opt).
ssolve_command(prunett) :- !, prunett.
ssolve_command(gentc(T,Opt)) :- !, gentc(T,Opt).
ssolve_command(gentc) :- !, gentc.
ssolve_command(writett) :- !, writett.
ssolve_command(writetc(Label)) :- !, writetc(Label).
ssolve_command(writetc) :- !, writetc.
ssolve_command(exporttt) :- !, exporttt.


