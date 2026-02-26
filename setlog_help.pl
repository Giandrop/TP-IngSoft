% setlog_help-1.0.1

%
% TODO pager doesn't work when {log} is run from swipl-win
%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%        The help sub-system   %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%                              %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%                Last revision: August 2025
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(library(strings)).

setlog_help(setlog) :- !,
  title('{log} help: table of contents',Title),
  setlog_symb(h,H),
  parameter('What',W),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  write({|string(Title,H,W)||
{Title}
  Call {H}(+{W}) where {W} is:
    syn:  {log} syntax w.r.t. Prolog and syntax of set terms
    cons: {log} constraints
    q:    quantifiers provided by {log}
    ts:   {log} type system
    sm:   specification of state machines
    next: Next, a simple environment for running state machines
    opt:  execution options and configurations
    cmd:  {log} user commands and Prolog-like predicates
    slog: Prolog predicates for accessing {log} facilities
    all:  to get all available help information

  Call setlog/0 to enter the {log} interactive environment.
|}).

setlog_help(all) :- !,
  with_pager(
    (title('{log} help',Title), write(Title),nl,
     (setlog_help(syn),
      more,
      setlog_help(st),
      more,
      setlog_help(cons),
      more,
      setlog_help(int),
      more,
      setlog_help(set),
      more,
      setlog_help(sin),
      more,
      setlog_help(rel),
      more,
      setlog_help(fun),
      more,
      setlog_help(q),
      more,
      setlog_help(ts),
      more,
      setlog_help(sm),
      more,
      setlog_help(next),
      more,
      setlog_help(opt),
      more,
      setlog_help(gen),
      more,
      setlog_help(pro),
      more,
      setlog_help(cs),
      more,
      setlog_help(thr),
      more,
      setlog_help(mon),
      more,
      setlog_help(cts),
      more,
      setlog_help(vcg),
      more,
      setlog_help(ttf),
      more,
      setlog_help(slog)
     ;
      true  % if more fails (user press 'q') we fail silently
     )
    )
  ).

setlog_help(syn) :- !,
  title('Syntactic differences w.r.t. standard Prolog',Title),
  setlog_symb(&,And),
  setlog_symb(or,Or),
  setlog_symb(neg,Neg),
  setlog_symb(naf,Naf),
  parameter(p,P),
  parameter(q,Q),
  setlog_symb(implies,Imp),
  setlog_symb(nimplies,Nimp),
  title('Set terms',Title2),
  parameter('Sterm',ITerm),
  new_concept('set terms',ST),
  setlog_symb(h,H),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  with_pager(
    write({|string(Title,And,Or,Neg,Naf,P,Q,Imp,Nimp,Title2,ST,ITerm,H)||
{Title}
  {And}
     is used in place of ',' to represent conjunction
  {Or}
     is used in place of ';' to represent goal disjunction
  {Neg}
     is used in place of \+ to represent simplified Constructive Negation
  {Naf}
     is used in place of \+ to represent Negation as Failure
  {P} {Imp} {Q}
    implemented as: neg(p) or q
  {P} {Nimp} {Q}
    implemented as: p & neg(q)

{Title2}
  In {log} terms of sort set are called {ST} and are interpreted terms.
  Call {H}(+{ITerm}) to get help on set terms, where {ITerm} is:
    es:  Extensional sets
    ii:  Integer intervals
    cp:  Cartesian product
    is:  Intensional sets
    ris: Restricted intensional sets
    st:  help on all set terms
|})).

setlog_help(st) :- !,
  with_pager(
    (setlog_help(es),
     setlog_help(ii),
     setlog_help(cp),
     setlog_help(is),
     setlog_help(ris)
    )
  ).

setlog_help(es) :- !,
  title('Extensional sets',Title),
  setlog_symb({},ESet),
  parameter(a,A),
  parameter('R',R),
  parameter('S',S),
  setlog_symb('{',OCB),
  setlog_symb(/,Bar),
  setlog_symb('}',CCB),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  write({|string(Title,ESet,A,R,S,OCB,Bar,CCB)||
{Title}
  Let {S} be a variable, {A} be any term, {R} be any set term, and \/ be set union.
  Then an extensional set is a set term of the following forms:
    {S}
      set terms can be variables; in this case the cardinality of {S} is finite
      but unknown
    {ESet}
      denotes the empty set
    {OCB}{A} {Bar} {R}{CCB}
      denotes the set {{A}} \/ {R}

  {log} provides a more convinient notation for extensional sets. For example,
  {a / {b / R}} can be written {a,b / R}; and {a / {b / {}}} can be written
  {a,b,c}.
|}).

setlog_help(ii) :- !,
  title('Integer intervals',Title),
  parameter(m,M),
  parameter(n,N),
  setlog_symb(int,INT),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  write({|string(Title,INT,M,N)||
{Title}
  Let {M} and {N} be variables or integer numbers and let Z be the set of integer
  numbers. Then an integer interval is a set term of the form {INT}({M},{N}), denoting
  the set {x | x in Z & {M} =< x =< {N}}. If n < m then {INT}({M},{N}) denotes the empty
  set. {M} and {N} can participate in integer constraints.
|}).

setlog_help(cp) :- !,
  title('Cartesian product',Title),
  parameter('A',A),
  parameter('B',B),
  setlog_symb(cp,CP),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  write({|string(Title,CP,A,B)||
{Title}
  A Cartesian product is a set term of the form {CP}({A},{B}), denoting the set
  {[x,y] | x in {A} & y in {B}}, where {A} and {B} can be variables, extensional sets or
  Cartesian products.
|}).

setlog_help(is) :- !,
  title('Intensional sets',Title),
  setlog_symb('{',OCB),
  setlog_symb('}',CCB),
  setlog_symb(':',SC),
  setlog_symb(exists,EX),
  parameter('X',X),
  parameter('G',G),
  parameter('V',V),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
write({|string(Title,OCB,CCB,SC,EX,X,G,V)||
{Title}
  Let {G} be a {log} goal containing variable {X} which is not used anywhere else,
  then an intentional set is a set term of the following forms (see Sect. 5.2 in
  the user's manual):
    {OCB}{X} {SC} ({G}){CCB} 
    {OCB}{X} {SC} {EX}({V},{G}){CCB}
      if {V} is a variable local to G
    {OCB}{X} {SC} {EX}([{V},...],{G}){CCB}
      if {V},... are variables local to {G}
|}).

setlog_help(ris) :- !,
  title('Restricted intensional sets (RIS)',Title),
  setlog_symb(ris,RIS),
  setlog_symb(in,IN),
  setlog_symb(is,Is),
  parameter('V',V),
  parameter('C',C),
  parameter('D',D),
  parameter('G',G),
  parameter('P',P),
  parameter(t,T),
  new_concept('control term',CT),
  new_concept('domain',Dom),
  new_concept('parameter',Param),
  new_concept('filter',F),
  new_concept('pattern',Patt),
  new_concept('functional predicates',FP),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  with_pager(
    write({|string(Title,RIS,C,CT,IN,D,V,Param,F,FP,G,T,P,Dom,Patt,Is)||
{Title}
  Let {C} be a variable, a nested closed list including only distinct variables or
  a term of the form [X|Y] or {X/Y}, where X and Y are distinct variables. In
  this case {C} is called {CT}. In all cases all the variables in {C} must
  not be used anywhere else. Let {V} be a variable distinct from all the variables
  in {C} and not used anywhere else. {V} is called {Param}. Let {G} be a {log} goal,
  called {F}. Let {P} be a conjunction of {FP}. p(x,...,y) is
  a functional predicate iff for each x,... there is only one y such that
  p(x,...,y) holds. The {Is} predicate (see h(int)) is a functional predicate
  w.r.t. its first argument. Then a RIS is a set term of the form:
 
  {RIS}({C} in {D},[{V},...],{G},{T},{P})
  
  where {D}, called {Dom}, can be any set term including a RIS, and {T}, called
  {Patt}, is any term but a RIS. In this case the RIS denotes the set 
  {x | exists([{C},{V},...],{C} in {D} & {G} & x={T} & {P})}. Note that RIS admit a list of
  parameters.
  
  {log} also provides the following simplified forms of RIS:
  
  {RIS}({C} in {D},[{V},...],{G})
    implemented as {RIS}({C} in {D},[{V},...],{G},{C},true)
  {RIS}({C} in {D},{G})
    implemented as {RIS}({C} in {D},[],{G},{C},true)

  Functional predicates can be removed if the let/3 predicate (see h(q)) is
  conveniently used as {G}. For example, instead of:
                      ris(X in D,[Y],Y in B,X,Y is X + 1)
  write
                      ris(X in D,let([Y],Y is X + 1, Y in B))
|})).


setlog_help(cons) :- !,
  title('{log} constraints',Title),
  setlog_symb(h,H),
  parameter('What',W),
  parameter(t,T),
  parameter(u,U),
  setlog_symb(=,Eq),
  setlog_symb(neq,Neq),
  setlog_symb(set,Set),
  setlog_symb(pair,Pair),
  setlog_symb(integer,Int),
  setlog_symb(rel,Rel),
  setlog_symb(pfun,Pfun),
  new_concept('sort constraints',Sort),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  with_pager(
    write({|string(Title,T,U,Eq,Neq,Set,Pair,Int,Rel,Pfun,H,W,Sort)||
{Title}
  The following constraints apply to any {log} terms {T} and {U}:
    {T} {Eq} {U}
      denotes equality. When {T} and {U} are set terms, equality is interpreted,
      otherwise Prolog unification is applied.
    {T} {Neq} {U}
      denotes the negation of equality (not equal)
    {Set}({T})
      {T} is a set term
    {Pair}({T})
      {T} is an ordered pair, i.e. {T} unifies with [_,_]
    {Int}({T})
      {T} is an integer variable or number
    {Rel}({T})
      {T} is a binary relation, i.e. is a set of ordered pairs
    {Pfun}({T})
      {T} is a partial function, i.e. is a set of ordered pairs such that if two
      pairs have the same first component then they have the same second
      component
  
  Besides the negation of {Set}, {Pair}, {Int}, {Rel} and {Pfun} is obtained by
  preffixing their names with 'n'. For example 'nrel', 'nintiger'. These
  constraints are called {Sort}.
  
  The remaining constraints available in {log} are divided in the following
  categories; get help on them with {H}(+{W}) where {W} is one of the following:
    int: Constraints dealing with integer arithmetic (e.g. <, =<, is, etc.)
    set: Constraints dealing with the Boolean algebra of sets (e.g. union,
         intersection, membership, difference, etc.)
    sin: Constraints relating sets with integers (e.g. cardinality, minimum of a
         set, etc.)
    rel: Constraints dealing with relation algebra (e.g. domain, composition,
         converse, identity, relational image, etc.)
    fun: Constraints dealing with functions (e.g. function application,
         functional composition, domain of a function, etc.)
|})).

setlog_help(int) :- !,
  title('{log} constraints for integer arithmetic',Title),
  parameter(n,N),
  parameter(d,D),
  parameter(e,E),
  setlog_symb(is,Is),
  setlog_symb(=<,Lt),
  setlog_symb(<,L),
  setlog_symb(>=,Gt),
  setlog_symb(>,G),
  setlog_symb(=:=,Eq),
  setlog_symb(=\=,Neq),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  with_pager(
    write({|string(Title,N,D,E,Is,Lt,L,Gt,G,Eq,Neq)||
{Title}
  Let {N} be a variable or an integer number, and {D} and {E} integer expressions.
  Then, the following constraints are interpreted as indicated after evaluating
  {D} and {E}.
    {N} {Is} {E}
      equality in the set of integer numbers
    {D} {Lt} {E}
      {D} is less than or equal to {E}
    {D} {L} {E}
      {D} is less than {E}
    {D} {Gt} {E}
      {D} is greater than or equal to {E}
    {D} {G} {E}
      {D} is greater than {E}
    {D} {Eq} {E}
      equality in the set of integer numbers
    {D} {Neq} {E}
      negation of {Eq}
      
  Note that in {D} = {E} both arguments remain uninterpreted (not evaluated) which
  in general is not what users want. Use {Is} or {Eq} instead.
|})).


setlog_help(set) :- !,
  title('{log} constraints of the Boolean algebra of sets',Title),
  parameter('A',A),
  parameter('B',B),
  parameter('C',C),
  parameter(t,T),
  setlog_symb(in,In),
  setlog_symb(un,Un),
  setlog_symb(nun,Nun),
  setlog_symb(disj,Disj),
  setlog_symb(inters,Int),
  setlog_symb(subset,Sub),
  setlog_symb(ssubset,Ssub),
  setlog_symb(diff,Diff),
  setlog_symb(ndiff,Ndiff),
  setlog_symb(sdiff,Sdiff),
  setlog_symb(less,Less),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  with_pager(
    write({|string(Title,A,B,C,T,In,Un,Disj,Int,Sub,Ssub,Diff,Sdiff,Less,Nun,Ndiff)||
{Title}
  Let {A}, {B} and {C} be set terms, and {T} any term. Let ':' be set membershio, \/ be
  set union, /\ be set intersection, / set difference and =< the subset
  relation. Then:
    {T} {In} {A}
      denotes set membership, i.e. {T} : {A}
    {Un}({A},{B},{C})
      denotes set union, i.e. {C} = {A} \/ {B}
    {Disj}({A},{B})
      is true iff {A} and {B} are disjoint, i.e. {A} /\ {B} = {}
    {Int}({A},{B},{C})
      denotes set intersection, i.e. {C} = {A} /\ {B}
    {Sub}({A},{B})
      denotes the subset relation, i.e. {A} =< {B}
    {Ssub}({A},{B})
      denotes strict subset, i.e {A} =< {B} & {A} neq {B}
    {Diff}({A},{B},{C})
      denotes set difference, i.e. {C} = {A} \ {B}
    {Sdiff}({A},{B},{C})
      denotes symmetric set difference, i.e. {C} = ({A} \ {B}) \/ ({B} \ {A})
    {Less}({A},{T},{B})
      denotes {B} = {A} \ {{T}}

  {log} also provides the negative counterparts of the above constraints by
  prefixing the constraint name with 'n'. For example {Nun} is the negation of {Un},
  and {Ndiff} is the negation of {Diff}.
|})).

setlog_help(sin) :- !,
  title('{log} constraints relating sets with integers',Title),
  parameter('S',S),
  parameter('D',D),
  parameter(n,N),
  setlog_symb(size,Size),
  setlog_symb(sum,Sum),
  setlog_symb(smin,Smin),
  setlog_symb(smax,Smax),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  write({|string(Title,S,D,N,Size,Sum,Smin,Smax)||
{Title}
  Let {S} be an extensional set or an interval; {D} an extensional set, an interval
  or an intensional set of non-negative integers; and {N} a variable or an integer
  number. Then:
  {Size}({S},{N})
    denotes set cardinality, i.e. |{S}| = {N}
  {Sum}({D},{N})
    denotes the sum ({N}) of all the elements of a set ({D})
  {Smin}({S},{N})
    denotes the minimum ({N}) a of set ({S})
  {Smax}({S},{N})
    denotes the maximum ({N}) a of set ({S})
  
  See commands show_min and fix_size in h(cs).
|}).

setlog_help(rel) :- !,
  title('{log} constraints for set relation algebra',Title),
  parameter('A',A),
  parameter('B',B),
  parameter('R',R),
  parameter('S',S),
  parameter('T',T),
  setlog_symb(dom,Dom),
  setlog_symb(inv,Inv),
  setlog_symb(ran,Ran),
  setlog_symb(comp,Comp),
  setlog_symb(id,Id),
  setlog_symb(dres,Dres),
  setlog_symb(rres,Rres),
  setlog_symb(dares,Dares),
  setlog_symb(rares,Rares),
  setlog_symb(rimg,Rimg),
  setlog_symb(oplus,Oplus),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  with_pager(
    write({|string(Title,A,B,R,S,T,Dom,Inv,Ran,Comp,Id,
                   Dres,Rres,Dares,Rares,Rimg,Oplus)||
{Title}
  Let {A} and {B} be any set terms but a RIS, and let {R}, {S} and {T} be extensional
  set terms or Cartesian products. Let dom(Q) be the domain of binary relation
  Q and \/ be set union. Then:
    {Dom}({R},{A})
      is true iff {A} = {x | (exists y : [x,y] in {R})}.
      {Dom} is called domain.
    {Inv}({R},{S})
      is true iff {S} = {[x,y] | [y,x] in {R}}.
      {Inv} is called converse.
    {Ran}({R},{A})
      is true iff {A} = {y | (exists x : [x,y] in {R})}.
      {Ran} is called range.
    {Comp}({R},{S},{T})
      is true iff {T} = {[x,z] | (exists y : [x,y] in {R} & [y,z] in {S})}.
      {Comp} is called composition.
    {Id}({A},{R})
      is true iff {R} = {[x,x] | x in {A}}.
      {Id} is called identity.
    {Dres}({A},{R},{S})
      is true iff {S} = {[x,y] | [x,y] in {R} & x in {A}}.
      {Dres} is called domain restriction.
    {Rres}({R},{A},{S})
      is true iff {S} = {[x,y] | [x,y] in {R} & y in {A}}.
      {Rres} is called range restriction.
    {Dares}({A},{R},{S})
      is true iff {S} = {[x,y] | [x,y] in {R} & x nin {A}}.
      {Dares} is called domain anti-restriction.
    {Rares}({R},{A},{S})
      is true iff {S} = {[x,y] | [x,y] in {R} & y nin {A}}.
      {Rares} is called range anti-restriction.
    {Rimg}({R},{A},{B})
      is true iff {B} = {y | (exists x : [x,y] in {R} & x in {A})}.
      {Rimg} is called relational image.
    {Oplus}({R},{S},{T})
      is true iff {T} = {[x,y] | [x,y] in {R} & x nin dom({S})} \/ {S}.
      {Oplus} is called overriding.

  {log} also provides the negative counterparts of the above constraints by
  prefixing the constraint name with 'n'. For example 'ndom' is the negation of
  {Dom}, and 'ninv' is the negation of {Inv}.
|})).


setlog_help(fun) :- !,
  title('{log} constraints dealing with functions',Title),
  parameter('F',F),
  parameter('G',G),
  parameter('H',H),
  parameter(t,T),
  parameter(u,U),
  parameter(v,V),
  setlog_symb(apply,App),
  setlog_symb(applyTo,Appt),
  setlog_symb(compf,Comp),
  setlog_symb(dompf,Dom),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  write({|string(Title,F,G,H,T,U,V,App,Appt,Comp,Dom)||
{Title}
  In {log} functions are set of ordered pairs, i.e. functions are binary
  relations. Let {F} and {G} be extensional set terms or Cartesian products; let {H}
  be an extensional set term, Cartesian product or RIS; and let {T} and {U} be any
  terms but Cartesian product or RIS. Then:
    {App}({F},{T},{U})
      is true iff {F} is a function (i.e. pfun({F})) and [{T},{U}] in {F}
    {Appt}({F},{T},{U})
      is true iff comp({[{T},{T}]},{F},{[{T},{U}]})
    {Comp}({F},{G},{T})
      is true iff pfun({F}) & pfun({G}) & pfun({H}) & 
                  {H} = {[x,z] | (exists y : [x,y] in {F} & [y,z] in {G})}
    {Dom}({H},{T})
      is true iff pfun({H}) & {T} = {x | (exists y : [x,y] in {H})}

  {log} also provides the negative counterparts for {App}, {Comp} and {Dom} by
  prefixing the constraint name with 'n'. For example 'ndompf' is the negation
  of {Dom}. The negation of {Appt} is provided in the setloglibpf.slog and
  setloglib_tc.slog libraries where is called 'n_applyTo'.
|}).


setlog_help(q) :- !,
  title('Quantifiers provided by {log}',Title),
  parameter('C',C),
  parameter('D',D),
  parameter('G',G),
  parameter('H',H),
  parameter('V',V),
  parameter('W',W),
  parameter('P',P),
  parameter('X',X),
  parameter('A',A),
  setlog_symb(foreach,Fe),
  setlog_symb(nforeach,Nfe),
  setlog_symb(exists,Ex),
  setlog_symb(nexists,Nex),
  setlog_symb(let,L),
  setlog_symb(nlet,Nl),
  setlog_symb(forall,Fa),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  with_pager(
    write({|string(Title,C,D,G,H,V,P,Fe,Nfe,Ex,Nex,L,Nl,Fa,X,A,W)||
{Title}
  Some of the quantifiers provided by {log} are the following (see more in Sect.
  6 of the user's manual). Let {C}, {D}, {G}, {V} and {P} be as in RIS(see h(ris)). Let {H}
  be a {log} goal containing variable {X} which is not used anywhere else, and let
  {A} be a variable, an extensional set, an interval or an intensional set. Let
  \forall be the universal quantifier (do not confuse it with {Fa}) and let
  \exists be the existential quantifier (do not confuse it with {Ex}). Then:
    {Fe}({C} in {D},{G})
      denotes (\forall {C} : {C} in {D} ==> {G}). {Fe} is called restricted universal
      quantifier (RUQ).
    {Nfe}({C} in {D},{G})
      denotes (exists {C} : {C} in {D} & neg({G}))
    {Ex}({C} in {D},{G})
      denotes (exists {C} : {C} in {D} & {G}). {Ex} is called restricted existential
      quantifier (REQ).
    {Nex}({C} in {D},{G})
      denotes (\forall {C} : {C} in {D} ==> neg({G}))
    {L}([{V},...],{P},{G})
      denotes (exists {V},... : {P} & {G})
    {Nl}([{V},...],{P},{G})
      denotes (exists {V},... : {P} & neg({G}))
    {Fa}({X} in {A}, {H})
    {Fa}({X} in {A}, {Ex}({W},{H}))
    {Fa}({X} in {A}, {Ex}([{W}...],{H}))
      {W},... are variables local to {H}

  If it is necessary to introduce existential variables in {Fe} then use {L}.
  For example, foreach([X,Y] in R, let([V], V is Y + 1, V in A)) introduces {V} as
  an existential variable.
  
  Usually users only need {Fe}, {Ex} and {L}. The negation of {Fe} is
  {Ex} and vice versa; the negation of {L} is {Nl} and vice versa.
  
  All quantifiers but {Fa} can be used as constraints. See {Fa} in Sect. 6.2 of
  the user's manual.
  
  Use {Ex} and {L} to avoid the introduction of existential variables in
  user-defined predicates. {log} can deal with existential variables introduced
  by means of {L}.
|})).


setlog_help(ts) :- !,
  title('{log} type system',Title),
  parameter(t,T),
  parameter(u,U),
  parameter(atom,At),
  parameter(cons,Cons),
  parameter(a,A),
  parameter('V',V),
  setlog_symb(int,Int),
  setlog_symb(str,Str),
  setlog_symb(enum,Enum),
  setlog_symb(sum,Sum),
  setlog_symb(set,Set),
  setlog_symb(rel,Rel),
  setlog_symb('[',Osb),
  setlog_symb(']',Csb),
  setlog_symb(':',SC),
  setlog_symb(dec,Dec),
  setlog_symb(dec_p_type,Decp),
  setlog_symb(dec_pp_type,Decpp),
  setlog_symb(def_type,DT),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  with_pager(
    write({|string(Title,Int,Str,Enum,Sum,Osb,Csb,DT,
                   Set,Rel,T,U,At,SC,A,Cons,V,Dec,Decp,Decpp)||
{Title}
  {log} type system supports the following types:
    {At}
      any Prolog atom different from {Int}, {Str} and any atom appearing in {Enum} and
      {Sum} declarations can be a type, called basic or uninterpreted type. The
      elements of {At} are terms of the form {At}{SC}{A} where {A} is a Prolog
      atom or an integer number.
    {Int}
      is the type of the integer numbers
    {Str}
      is the type of the character strings
    {Enum}([{Cons},...])
      is an enumerated type whose elements ar the elements of the list
      [{Cons},...], where {Cons} is a Prolog atom. The list must be a set of at
      least two elements. The elements cannot appear in any other type
      definition.
    {Sum}([{Cons},{Cons}({T},...),...])
      is a union or disjoint sum type whose elements are built by the
      constructors {Cons}. {Cons} can be any atom not used in the definition of
      other types. If {Cons} has arguments they must be types.
    {Osb}{T},{U}{Csb}
      is a Cartesian product type. Its elements are ordered pairs. {T} and {U} are
      types.
    {Set}({T})
      is the powerset type whose elements are sets of type {T}.
    {Rel}({T},{U})
      is a synonym for {Set}({Osb}{T},{U}{Csb}), i.e. the type of all binary relations of
      type {Osb}{T},{U}{Csb}.

  If {V} is a variable and {T} is a type, {Dec}({V},{T}) is a predicate stating that {V} is
  of type {T}. {Decp}(p({T},{U}...)) declares the type of the first argument of
  predicate p to be {T}, of the second argument to be {U}, and so forth. This
  declaration must precede p's definition. The declaration {Decpp} is used
  to declare the type of polymorphic predicates. {DT}({A},{T}) declares {A}, an
  atom, as a synonym of type {T}. From this point on {A} can be used in place of {T}.
|})).


setlog_help(sm) :- !,
  title('Specification of states machines',Title),
  parameter('V',V),
  parameter('V_',VP),
  parameter(p,P),
  parameter(h,H),
  setlog_symb(parameters,Par),
  setlog_symb(variables,Var),
  setlog_symb(axiom,Ax),
  setlog_symb(invariant,Inv),
  setlog_symb(initial,Ini),
  setlog_symb(operation,Op),
  setlog_symb(theorem,Thm),
  setlog_symb(proof_,Proof),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  with_pager(
    write({|string(Title,V,P,Par,Var,Ax,Inv,Ini,Op,Thm,Proof,VP,H)||
{Title}
  Let {V} be a variable and {P} the head of a predicate. Then:
    {Par}([{V},...])
      declares {V},... to be the parameters (optional). [{V},...] must be a set of
      variables.
    {Var}([{V},...])
      declares {V},... to be the state variables (at least one variable). [{V},...]
      must be a set of variables.
    {Ax}({P})
      declares {P} to be an axiom (optional). The arguments of {P} can only be
      parameters.
    {Inv}({P})
      declares {P} to ba an invariant (at least one). The arguments of {P} can only
      be parameters or state variables.
    {Ini}({P})
      declares {P} to be the predicate defining the initial state. The arguments
      of {P} can only be parameters or state variables.
    {Op}({P})
      declares {P} to be an operation (at least one). The arguments of {P} can only
      be parameters, state variables or next-state variables (i.e. if {V} is a
      state variable, {VP} is the corresponding next-state variable).
    {Thm}({P})
      declares {P} to be a theorem (optional). The arguments of {P} can only be
      parameters or state variables.
    {Proof}{P}
      is the proof of theorem {P}. The arguments of {Proof}{P} must be those of {P}.
      The body of {Proof}{P} must be of the form neg({H} & ... implies {P}) where {H}
      must be an axiom, invariant, operation or theorem already declared.

  The order of declarations is the one given above except that {Thm} can be
  declared anywhere in the specification after the first axiom. A {Thm}
  declaration must be followed by the corresponding {Proof} predicate.
|})).


setlog_help(next) :- !,
  title('Next: an environment for executing state machines',Title),
  parameter(p,P),
  parameter(q,Op),
  parameter(s,S),
  parameter(a,A),
  parameter(g,G),
  parameter(i,I),
  parameter(n,N),
  parameter(step,Call),
  parameter('I',V),
  parameter('O',X),
  setlog_symb(initial,Ini),
  setlog_symb(>>,Nxt),
  setlog_symb(':',SC),
  setlog_symb(setpp,Set),
  setlog_symb(these_parameters,TP),
  new_concept(assignment,Agn),
  new_concept('double lists',DL),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  with_pager(
    write({|string(Title,Ini,P,A,V,Nxt,Op,Agn,SC,S,X,G,I,DL,Call,N,Set,TP)||
{Title}
  Next can be used on a state machine specification only if:
    1. The specification has been typechecked.
    2. The VCG has been called on the specification (see h(vcg))
    3. The VC file has been consulted

  Let:
    {V} be an input variable
    {X} be an output variable
    {G} be a ground term
    {Op} be an operation or an invariant
    {A} be an {Agn}. An assignment is a term of the form {V}{SC}{X} or {V}{SC}[[{G},...]].
      Terms of the form [[{G},...]] are called {DL}. 
    {S} be an invariant
    {N} be an integer number greater than 1
    {I} be the atom {Ini} or the head of predicate instantiating all the state
      variables
    {Call} be a term of the form {Op}({A},{X},...) or {N}{SC}{Op}({A},{X},...)
  If an assignment of the form {V}{SC}[[{G},...]] is an argument in {Op} then all the
  double lists making part of arguments in {Op} must be of the same length.
  
  Then, the following executions can be run:
    {I} {Nxt} {Call} {Nxt} {Call} {Nxt} ...
      to execute the provided sequence of steps from the state set by {I}. The
      after-state of a step is used as the before-state in the next one.
      Assignments set values for the input variables in each step.
    [{I}] {Nxt} {Call} {Nxt} {Call} {Nxt} ...
      as above but the whole state trace is printed
    {I}{SC}[{S},...] {Nxt} {Call} {Nxt} {Call} {Nxt} ...
      as the first one but also Next checks that every next-state satisfies
      each invariant in [{S},...]. The user is informed if an invariant is not
      satisfied at some step.
    [{I}]{SC}[{S},...] {Nxt} {Call} {Nxt} {Call} {Nxt} ...
      combines the second and third cases

  If the specification uses paremeters then execute the command {Set}/1 before
  running any simulation or make sure a predicate named {TP} is in
  scope.
|})).


setlog_help(opt) :- !,
  title('Execution options and configurations',Title),
  subtitle('Prover options',ST1),
  subtitle('Other execution options',ST2),
  subtitle('Configurations',ST3),
  parameter(opt,Opt),
  setlog_symb(mode,Mod),
  setlog_symb(prover_all_strategies,PAS),
  setlog_symb(subset_unify,SU),
  setlog_symb(un_fe,UF),
  setlog_symb(comp_fe,CF),
  setlog_symb(oplus_fe,OF),
  setlog_symb(ran_fe,RF),
  setlog_symb(noirules,NI),
  setlog_symb('strategy(ordered)',SO),
  setlog_symb(try,Try),
  setlog_symb(tryp,Tryp),
  setlog_symb(prover_all,PA),
  setlog_symb(prover_all_single,PASi),
  new_concept(configuration,Conf),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  with_pager(
    write({|string(Title,ST1,ST2,ST3,Mod,PAS,SU,UF,CF,
                   OF,RF,NI,SO,Opt,Conf,Try,Tryp,PA,PASi)||
{Title}
{ST1}
  The following execution options can be set with commands {Mod} (see h(cs))
  and {PAS} (see h(thr)) and can be passed to setlog* (see
  h(slog)). This list is part of the default value of {PAS}.
    {SU}
      implements set equality as a double set inclusion
    {UF}
      implements union in terms of RUQ (see h(q))
    {CF}
      implements composition in terms of RUQ (see h(rel))
    {OF}
      implements overriding in terms of RUQ (see h(rel))
    {RF}
      implements range in terms of RUQ
    {NI}
      deactivates the execution of optional inference rules
    {SO}
      modifies the constraint solving order

{ST2}
  The predicates labeled with (eo) in h(cs), h(cts) and h(mon) can be used as
  execution options and thus passed to setlog* (see h(slog)).

{ST3}
  Let {Opt} be an execution option. A {Conf} is a term of the form:
    []
      default configuration
    [{Opt},...]
      every execution option in the list is set
    {Try}([[{Opt},...],...])
      list of lists of execution options
      keyword {Try} refers to try each list after the other until one succeeds
    {Tryp}([[{Opt},...],...])
      list of lists of execution options
      keyword {Tryp} refers to try each list in a different thread (see h(thr))
    {Try}({PA})
      {PA} = powerset(default value of prover_all_strategies) (see h(thr))
    {Tryp}({PA}) 
    {Try}({PASi})
      {PASi} = default value of prover_all_strategies (see h(thr))
    {Tryp}({PASi})
|})).


setlog_help(cmd) :- !,
  title('User commands and standard predicates',Title),
  setlog_symb(h,H),
  parameter('What',W),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  write({|string(Title,H,W)||
{Title}
  Call {H}(+{W}) where {W} is:
    gen: general predicates and user commands
    pro: Prolog-like predicates
    cs:  predicates and commands controlling constraint solving
    thr: commands to run goals using threads, timeouts and execution options
    mon: commands for execution monitoring
    cts: commands to work with typed programs
    vcg: VCG commands  
    ttf: commands for test case generation
|}).


setlog_help(gen) :- !,
  title('General commands',Title),
  parameter('G',G),
  parameter('C',C),
  parameter(f,F),
  setlog_symb(halt,Halt),
  setlog_symb(prolog_call,Pcall),
  setlog_symb(call,Call),
  setlog_symb(solve,Sol),
  setlog_symb('!',Cut),
  setlog_symb(consult_lib,CL),
  setlog_symb(add_lib,AL),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  write({|string(Title,G,C,F,Halt,Pcall,Call,Sol,Cut,CL,AL)||
{Title}
  {Halt}/0
    to leave the {log} interactive environment (back to the host environment)
  {Pcall}({G})
    to call any Prolog goal {G} from {log}
  {Call}({G}), {Call}({G},{C})
    to call a {log} goal {G}, possibly getting constraint {C}
  {Sol}({G})
    like {Call}({G}) but all constraints generated by {G} are immediately solved
  {G}{Cut}
    to make a {log} goal G deterministic
  {CL}/0
    to consult the {log} library file setloglib.slog
  {AL}({F})
    to add any file F to the {log} library
|}).


setlog_help(pro) :- !,
  title('Prolog-like predicates',Title),
  setlog_symb(read,R),
  setlog_symb(write,W),
  setlog_symb(assert,A),
  setlog_symb(consult,C),
  setlog_symb(listing,L),
  setlog_symb(abolish,B),
  setlog_symb(nl,N),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  write({|string(Title,R,W,A,C,L,B,N)||
{Title}
  These Prolog predicates are directly available from {log}:
    {R}/1
    {W}/1
    {A}/1
    {C}/1
    {L}/0
    {B}/0
    {N}/0
|}).


setlog_help(cs) :- !,
  title('Commands controlling constraint solving',Title),
  parameter('G',G),
  parameter('C',C),
  parameter('S',S),
  parameter('X',X),
  parameter(a,A),
  parameter('Solver',Sol),
  parameter('Mode',Mod),
  setlog_symb(delay,D),
  setlog_symb(strategy,Str),
  setlog_symb(irules,I),
  setlog_symb(neq_elim,N),
  setlog_symb(ran_elim,R),
  setlog_symb(comp_elim,CE),
  setlog_symb(labeling,L),
  setlog_symb(label,NL),
  setlog_symb(int_solver,IS),
  setlog_symb(mode,M),
  setlog_symb(cfirst,CF),
  setlog_symb(ordered,O),
  setlog_symb(no,NO),
  setlog_symb(clpq,Q),
  setlog_symb(clpfd,F),
  setlog_symb(solver,V),
  setlog_symb(prover,P),
  setlog_symb(groundsol,GS),
  setlog_symb(fix_size,FS),
  setlog_symb(show_min,SM),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  with_pager(
    write({|string(Title,G,C,S,X,A,Sol,Mod,D,Str,I,N,R,CE,
                   L,NL,IS,M,CF,O,NO,Q,F,V,P,GS,FS,SM)||
{Title}
  {GS}/0, {NO}{GS}/0 (eo)
    to activate/deactivate the generation of ground solutions
  {D}({G},{C})
    to delay execution of {G} until either {C} holds or the computation ends 
    ({G}, {C} {log} goals)
  {Str}({S}) (eo)
    to change goal atom selection strategy to {S}
    values for {S}: {CF}, {O}, {CF}([{A},...]) ([{A},...] is a list of atoms)
  {NO}{I}/0, {I}/0 (eo)
    to deactivate/activate inference rules
    default: {I}
  {NO}{N}/0, {N}/0 (eo)
    to deactivate/activate elimination of neq-constraints
    default: {N} - possible unreliable solutions when {NO}{N}
  {NO}{R}/0, {R}/0 (eo)
    to deactivate/activate elimination of constraints of the form ran(R,{...})
    default: {R} - possible unreliable solutions when {NO}{R}
  {NO}{CE}/0, {CE}/0 (eo)
    to deactivate/activate complete rewriting of comp/3 constraints (see h(rel))
    default: {CE} - possible unreliable solutions when {NO}{CE}
  {L}({X})
    to force labeling for the domain variable {X}
  {NO}{NL}/0, {NL}/0 (eo)
    to deactivate/activate labeling on integer variables
    default: {NL} - possible unreliable solutions when {NO}{NL}
  {IS}({Sol}) (eo)
    to change the integer solver
    values for {Sol}: {Q} (CLP(Q)), {F} (CLP(FD))
    default: {Q}
  {M}({Mod})
    to change the solving strategy
    values for {Mod}: {V} (eo), {P}, {P}({[{A},...) ([{A},...] list of 
                     execution options, see h(opt))
    default: {P}([])
  {FS}/0, {NO}{FS}/0 (eo)
    to activate/deactivate the generation of solutions with minimum cardinality
    when the formula includes size/2 constraints (see h(sin))
  {SM}/0, {NO}{SM}/0 (eo)
    to activate/deactivate the generation of solutions showing the minumim
    cardinalities of sets involved in size/2 constraints (see h(sin))
|})).


setlog_help(thr) :- !,
  title('Commands to run goals using threads and timeouts',Title),
  parameter(mod,Mod),
  parameter(opt,Opt),
  parameter(conf,C),
  parameter(t,T),
  parameter('G',G),
  setlog_symb(prover_all_strategies,PAS),
  setlog_symb(all,All),
  setlog_symb(all_single,Alls),
  setlog_symb(p_t_solve,PTS),
  setlog_symb(timeout,TO),
  setlog_symb(t_solve,TS),
  new_concept(modifiers,Modi),
  new_concept(configuration,Conf),
  new_concept(timeout,CTO),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  with_pager(
    write({|string(Title,PAS,All,Alls,PTS,TO,TS,Mod,Opt,T,G,C,Modi,Conf,CTO)||
{Title}
  The following commands solve a goal by running several copies on an equal
  number of threads. In turn each thread is configured with a set of execution
  options (see h(opt)). In this way {log} increases the chances of solving the
  goal faster. The whole computation comes to an end as soon as a thread solves
  the goal.
  Let {Mod} be the {Modi} {All} or {Alls}; let {Opt} be an execution option
  (see h(opt)); let {G} be a goal; and let {T}, called {CTO}, be a positive
  integer number. Then:
    {PAS}([{Mod},[{Opt},...]])
      sets the current modifier and list of execution options
      if the parameter is a variable, it is bound to the current value
      default value: [{All},dl] where dl is the list of all prover execution
                     options (see h(opt))
    {TO}({T})
      sets the current timeout
    {TS}({G})
      executes {G} for as long as the current timeout 
    {PTS}({G})
      solves {G} by running it in parallel in multiple threads for as long as the
      current timeout. The number of threads and the combination of execution
      options for each thread depend on the current value of
      {PAS} as follows:
        {All}: all the combinations of execution options are used in an equal
             number of threads
        {Alls}: a thread is created for each execution option
    {TS}({G},{T},{C})
      executes {G} for as long as {T} using configuration {C} (see h(opt))
|})).

setlog_help(mon) :- !,
  title('Commands for execution monitoring',Title),
  parameter('G',G),
  parameter('T',T),
  parameter('Mode',Mod),
  setlog_symb(no,NO),
  setlog_symb(trace,Trace),
  setlog_symb(time,Time),
  setlog_symb(sat,Sat),
  setlog_symb(irules,IR),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  write({|string(Title,G,T,NO,Trace,Time,Mod,Sat,IR)||
{Title}
  {NO}{Trace}/0, {Trace}({Mod}) (eo)
    to deactivate/activate constraint solving tracing
    values for {Mod}: {Sat}, general tracing; {IR}, inference rules tracing
    default: {NO}{Trace}
  {Time}({G},{T})
    to get CPU time (in milliseconds) for solving goal {G}
|}).

setlog_help(cts) :- !,
  title('Commands to work with typed programs',Title),
  parameter(a,A),
  parameter(t,T),
  parameter(x,X),
  parameter('V',V),
  setlog_symb(type_check,TC),
  setlog_symb(no,NO),
  setlog_symb(idef_type,DT),
  setlog_symb(reset_types,RT),
  setlog_symb(type_of,TO),
  setlog_symb(type_decs,TD),
  setlog_symb(expand_type,ET),
  setlog_symb(td,Td),
  setlog_symb(pt,PT),
  setlog_symb(ppt,PPT),
  write({|string(Title,TC,NO,DT,I,RT,TO,TD,ET,A,T,V,X,Td,PT,PPT)||
{Title}
  Let {A} be an atom, let {T} be a type, let {V} be a variable. Then:
    {TC}/0, {NO}{TC}/0 (eo)
      to activate/deactivate type checking
    {RT}/0
      to delete all type information. Use this command before consulting a file
      when type checking is active.
    {DT}({A},{T})
      to declare {A} as a type synonym of {T}
    {TO}({A})
      if {A} is the head of a predicate, the command prints its type
    {TD}({X})
      prints type information depending on the value of {X}:
        {Td}:  all type declarations (cf. {DT}/2)
        {PT}:  the type of all non-polymorphic predicates
        {PPT}: the type of all polymorphic predicates
    {ET}({T},{V})
      {V} is bound to the result of unfolding type {T}  
|}).

setlog_help(vcg) :- !,
  title('VCG commands',Title),
  parameter(vc,VC),
  parameter(f,F),
  parameter(ext,E),
  parameter(t,T),
  parameter(conf,Conf),
  setlog_symb(vcg,VCG),
  setlog_symb(vcgce,G),
  setlog_symb(vcace,A),
  setlog_symb(findh,Find),
  setlog_symb(check_vcs_,C),
  setlog_symb('ERROR',Err),
  setlog_symb('OK',OK),
  setlog_symb('TIMEOUT',TO),
  new_concept('verification conditions',VCc),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  with_pager(
    write({|string(Title,VCG,G,A,Find,VC,F,C,T,Conf,E,Err,VCc,OK,TO)||
{Title}
  These commands work on typed state machines specified in {log} (see h(type)
  and h(sm)).
  {VCG}('{F}.{E}')
    generates a file named {F}-vc.{E} containing the {VCc} (VC)
    for the specification saved in file {F}.{E}. The following commands can be run
    after consulting {F}-vc.{E}.
  {C}{F}({T},{Conf})
    attempts to discharge all the VC generated for the specification. Each VC is
    run for at most {T} ms and using the configuration {Conf} (see h(thr)).
    The result of this command is a report describing the status of each VC. The
    status is one of: {OK}, the VC has been discharged; {Err}, the VC could not
    be discharged because {log} found a counterexample; and {TO}, {log} could
    not prove nor disprove the VC in {T} milliseconds.
  {C}{F}({Conf})
    implemented as {C}{F}(60000,{Conf})
  {C}{F}
    implemented as {C}{F}([])
    [] means the default configuration
  {G}({VC})
    prints a ground counterexample for verification condition {VC}
    only after {C}{F}* and if the status of {VC} is {Err}
  {A}({VC})
    prints an abstract counterexample for verification condition {VC}
    only after {C}{F}* and if the status of {VC} is {Err}
  {Find}
    attempts to find missing hypotheses for VC marked with {Err}
    there are four variants, see the user's manual
|})).


setlog_help(ttf) :- !,
  title('Commands for test case generation',Title),
  subtitle('Testing tactics',ST1),
  subtitle('Other commands',ST2),
  parameter(p,P),
  parameter(i,I),
  parameter(c,C),
  parameter(u,U),
  parameter(l,L),
  parameter('V',V),
  parameter(n,N),
  parameter(e,E),
  parameter(a,A),
  parameter(t,T),
  parameter(conf,Conf),
  setlog_symb(applydnf,DNF),
  setlog_symb(applysp,SP),
  setlog_symb(applyst,ST),
  setlog_symb(applyii,II),
  setlog_symb(applysc,SC),
  setlog_symb(applyex,EX),
  setlog_symb(ttf,TTF),
  setlog_symb(writett,WTT),
  setlog_symb(prunett,PTT),
  setlog_symb(gentc,GTC),
  setlog_symb(writetc,WTC),
  setlog_symb(exporttt,ETT),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  with_pager(
    write({|string(Title,ST1,ST2,DNF,SP,ST,II,SC,EX,TTF,WTT,PTT,GTC,WTC,ETT,
                   P,I,C,U,L,V,N,E,A,T,Conf)||
{Title}
  These commands work on state machines specified in {log} verifying the
  following:
    1. The specification has been typechecked (see h(type))
    2. The VCG has been called on the specification (see h(vcg))
    3. The resulting VC file has been consulted
  The process starts with command {TTF}/1 followed by {DNF}/1, see below.

{ST1}
  Let {P} the head of an operation, let {I} be an input variable of {P}; let {L} be a
  label of the testing tree; let {C}({U},...) be a constraint exactly as appearing
  in the operation; let {V} be a variable; let {N} be an integer number; and let {E}
  be a REQ (see h(q)) exactly as appearing in the operation. Then:
    {DNF}({P}({I},...))
      to apply the disjunctive normal form (DNF) testing tactic
      this must be the first tactic to be applied
    {SP}({L},{C}({U},...))
      to apply the standard partition (SP) testing tactic
    {ST}({L},{V})
      to apply the sum types (ST) testing tactic
    {II}({L},{V},[{N},...])
      to apply the integer intervals (II) testing tactic
    {SC}({L},{V})
      to apply the set cardinality (SC) testing tactic
    {EX}({L},{E})
      to apply the restricted existential quantifier (EX) testing tactic

{ST2}
  Let {A} be an atom; let {T} be a timeout (see h(thr)); let {Conf} be a configuration
  (see h(opt)); let {L} be a label in the testing tree.
    {TTF}({A})
      to initialize the test case generation process
      use this command to start the process for another operation
      {A} is used to name the test cases file (see {ETT} below)
    {WTT}/0
      to print the current testing tree
    {PTT}({T},{Conf})
      to prune unsatisfiable leaves of the current testing tree
      {T} and {Conf} are passed in to rsetlog/5 (see h(slog))
    {PTT}({Conf})
      implemented as {PTT}(60000,{Conf})
    {PTT}/0
      implemented as {PTT}(60000,[])
    {GTC}({T},{Conf})
      to generate test cases for the leaves of the current testing tree
      {T} and {Conf} are passed in to setlog_str/6 (see h(slog))
    {GTC}/0
      implemented as {GTC}(60000,[type_check]) (see h(opt))
    {WTC}({L})
      to print test case {L}
    {WTC}/0
      to print all test cases
    {ETT}
      to export test cases/specifications to a file named {A}_{P}-tt.slog
|})).

setlog_help(slog) :- !,
  title('Prolog predicates for accessing {log} facilities',Title),
  parameter('G',G),
  parameter(t,T),
  parameter('C',C),
  parameter('R',R),
  parameter(conf,Conf),
  parameter('N',N),
  parameter('V',V),
  parameter(f,F),
  parameter('Cl',Cl),
  parameter(p,P),
  setlog_symb(setlog,SL),
  setlog_symb(rsetlog,RSL),
  setlog_symb(setlog_str,SSL),
  setlog_symb(rsetlog_str,RSSL),
  setlog_symb(setlog_tc,TCSL),
  setlog_symb(setlog_consult,CSL),
  setlog_symb(consult_lib,CL),
  setlog_symb(setlog_clause,CLSL),
  setlog_symb(setlog_config,ConfSL),
  setlog_symb(success,S),
  setlog_symb(maybe,M),
  setlog_symb(time_out,TO),
  setlog_symb(failure,Fa),
% DON'T CHANGE INDENTATION BEYOND THIS POINT
  with_pager(
    write({|string(Title,G,T,C,R,Conf,N,V,SL,RSL,Fa,
                   SSL,RSSL,TCSL,CSL,CL,CLSL,ConfSL,F,Cl,P,S,M,TO)||
{Title}
  These predicates are meant to be called from Prolog to use {log} as a library.
  Let {G} be a goal, {T} a timeout (see h(thr)), {Conf} a configuration (see (h(opt)),
  and {C}, {R}, {N}, and {V} variables. Let {F} be a file name and {Cl} a clause. Then:
    {SL}(+{G},+{T},-{C},-{R},+{Conf})
      to execute {G} for at most {T} ms under configuration {Conf} getting the answer
      {R} and a list of constraints {C}
      {R} is one of: {S} if {G} terminates successfully within time {T}
                   {M} as {S} but the answer is not safe
                   {TO} if {G} does not terminate within time {T}
    type_check (see h(cts)) and groundsol (see h(cs)) have no effect if used
    in {Conf}, if needed use {SSL}/6
    {SL}(+{G},+{T},-{C},-{R})
      implemented as (see h(cs))
        {SL}({G},{T},{C},{R},try([[int_solver(clpfd)],[int_solver(clpq),final],
                            [noirules],[noneq_elim],[noran_elim]]))
    {SL}(+{G},-{C},-{R})
      implemented as {SL}({G},infinite,{C},{R},[])
    {SL}(+{G},-{C})
      implemented as {SL}({G},{C},_)
    {SL}(+{G})
      implemented as {SL}({G},_)
    {SL}/0
      to enter the {log} interactive environment
    {RSL}(+{G},+{T},-{C},-{R},+{Conf})
      same as {SL}/5 with reification on {R}
      if {G} terminates with failure then {R} = {Fa}
    {SSL}(+"{G}",['{N}'={V},...],+{T},-{C},-{R},+{Conf})
      first argument is a string
      implemented as
        term_string(T,"{G}",variable_names(['{N}'={V},...])),
        setlog(T,{T},{C},{R},{Conf})
    {SSL}(+"{G}",-{V},+{T},-{C},-{R},+{Conf})
      as above but {V} and {C} are bound to lists of strings corresponding to the
      list of equalities and constraint that {log} would normally return for {G}
    {SSL}(+"{G}",['{N}'={V},...],-{C},-{R})
      implemented as {SSL}("{G}",['{N}'={V},...],infinite,{C},{R},[])
    {SSL}(+"{G}",-{V},-{C},-{R})
      implemented as {SSL}("{G}",{V},infinite,{C},{R},[])
    {SSL}(+"{G}",['{N}'={V},...],-{C})
      implemented as {SSL}("{G}",['{N}'={V},...],infinite,{C},_)
    {SSL}(+"{G}",-{V},-{C})
      implemented as {SSL}("{G}",{V},infinite,{C},_)
    {SSL}(+"{G}",['{N}'={V},...])
      implemented as {SSL}("{G}",['{N}'={V},...],infinite,_)
    {SSL}(+"{G}",-{V})
      implemented as {SSL}("{G}",{V},infinite,_)
    {RSSL}(+"{G}",['{N}'={V},...],+{T},-{C},-{R},+{Conf})
      same as {SSL}/6 but with reification on {R} as in {RSL}/5
    {RSSL}(+"{G}",-{V},+{T},-{C},-{R},+{Conf})
      same as {SSL}/6 but with reification on {R} as in {RSL}/5
    {TCSL}(+"{G}",['{N}'={V},...],-{C})
      implemented as
        {SSL}("{G}",['{N}'={V},...],infinite,{C},_,[type_check]) (see h(cts))
    {TCSL}(+"{G}",-{V},-{C})
      implemented as {SSL}("{G}",{V},infinite,{C},_,[type_check]) (see h(cts))
    {CSL}('{F}')
      to consult a {log} file {F}
    {CL}/0
      to consult the {log} library file
    {CLSL}({Cl})
      to add a {log} clause {Cl} to the current {log} program
    {ConfSL}([{P},...])
      to modify some {log} configuration parameters
      {P} can be: path(Path), rw_rules(File), fd_labeling_strategy(SList)
|})).


setlog_help(_) :- !,
    throw(setlog_excpt('invalid argument')).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% auxiliary predicates
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

parameter(T,BT) :- atomics_to_string(['\33\[1m',T,'\33\[0m'],BT).

title(T,NT) :-
  string_upper(T,U),
  string_codes(U,CU),
  replace_setlog(CU,NCU),
  string_codes(S,NCU),
  atomics_to_string(['\33\[1m',S,'\33\[0m\n'],NT).

% replaces {LOG} for {log} in a help title
%
replace_setlog([],[]) :- !.
replace_setlog([123, 76, 79, 71, 125|Cs],[123,108, 111, 103, 125|Cs]) :- !.
replace_setlog([C|Cs],[C|Cs1]) :- replace_setlog(Cs,Cs1).

subtitle(T,NT) :-
  atomics_to_string(['\33\[1m',T,'\33\[0m'],NT).

% (1) when {log} is run from swipl-win some colors
%     and font effects aren't displayed correctly
%     and pagers don't work, so other
%     colors/effects are used and no pager is used
%
setlog_symb(T,RT) :-
  current_predicate(window_title/2),!,               % in swipl-win (1)
  atomics_to_string(['\33\[31m',T,'\33\[0m'],RT).
setlog_symb(T,RT) :-
  atomics_to_string(['\33\[1;31;40m',T,'\33\[0m'],RT).

new_concept(T,UT) :-
  current_predicate(window_title/2),!,               % in swipl-win (1)
  atomics_to_string(['\33\[34m',T,'\33\[0m'],UT).
new_concept(T,UT) :-
  atomics_to_string(['\33\[4m',T,'\33\[0m'],UT).

more :-
  (current_predicate(window_title/2) ->              % in swipl-win (1)
     write('\nPress ''enter'' to continue or ''q'' to quit'),
     get_single_char(C),
     (C = 113 -> fail ; true)
  ;
     true
  ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% The following code corresponds to the SWI-Prolog package
% named "pager" (https://www.swi-prolog.org/pack/list?p=pager)
%
% Author: Michael Hendricks michael@ndrix.org
%
% We modified the code by getting a valid pager if 'PAGER' isn't
% defined before calling setup_call_cleanup/3 and by setting up
% execution options for each possible pager.
%
% The original code doesn't seem to work well on Windows.
%
% The code is included here to avoid installation issues
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%% with_pager(:Goal)
%
%  Send output of Goal through the user's preferred pager.
%  The pager is only used if current_output is connected
%  to a terminal and there's a valid pager.  Otherwise,
%  send output directly to current_output.

:- meta_predicate with_pager(0).

% (1) when {log} is run from swipl-win no pager can be
%     used. so help is printed as it is in that case.
with_pager(Goal) :-
    stream_property(current_output,tty(true)),
    get_pager(Pager),
    \+current_predicate(window_title/2),           % not in swipl-win (1)
    !,
    setup_call_cleanup(
        with_pager_setup(Pager,PagerIn,Pid),
        with_output_to(PagerIn,Goal),
        with_pager_cleanup(PagerIn,Pid)
    ).
with_pager(Goal) :-
    call(Goal).

% set up a pager
with_pager_setup(Pager,PagerIn,Pid) :-
    arglist(Pager,AL),
    process_create(
        path(Pager),
        AL,
        [
            stdin(pipe(PagerIn)),
            stdout(std),
            process(Pid)
        ]
    ).

get_pager(Pager) :- getenv('PAGER',Pager),!.
get_pager(less) :- exists_file('/usr/bin/less'),!.
get_pager(more) :- exists_file('/usr/bin/more'),!.

arglist(less,["-R"]).
arglist(more,["-f"]).

% clean up after a pager
with_pager_cleanup(PagerIn,Pid) :-
    close(PagerIn),
    process_wait(Pid,_Status).



