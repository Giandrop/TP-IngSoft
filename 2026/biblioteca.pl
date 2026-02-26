% Biblioteca
variables([Libros, Info, Prestados]).

MSJ = {ok, error}.

def_type(nat, int).

dec_p_type(invNat(nat)).
invNat(N) :- N >= 0.

% def_type(msj, {ok, error}).
% def_type(msj, enum([ok, error])).
def_type(libros, rel(isbn, nat)).
def_type(info, rel(isbn, [titulo, autor])).
def_type(prestados, rel(nrosocio, isbn)).


% Invariantes de tipos

dec_p_type(invTipo(libros, info, prestados)).
invTipo(Libros, Info, Prestados) :-
    pfun(Libros) &
    % let([Nat], ran(Libros, Nat) & subset(Nat, nat)) &
    pfun(Info) &
    pfun(Prestados).

% \begin{schema}{BibliotecaInv}
% Biblioteca
% \where
% \ran prestados \subseteq \dom libros
% \end{schema}

% \begin{schema}{BibliotecaInv2}
% Biblioteca
% \where
% \forall l : ISBN | l \inbag libros @ \#(prestados \rres \set{l}) \leq libros \# l
% \end{schema}

% invariant(bibliotecaInv).
% dec_p_type(bibliotecaInv(libros, prestados)).
% bibliotecaInv(Libros, Prestados) :-
%     ran(Prestados, A) & dom(Libros, B) & subset(A, B).

% #############################################################################

% invariant(bibliotecaInv2).
% dec_p_type(bibliotecaInv2(libros, prestados)).
% bibliotecaInv2(Libros, Prestados) :-
%     foreach(L in isbn, dom(Libros, A) & L in A implies size(B, N) & rres(Prestados, {L}, B) & applyTo(Libros, L, M) & N =< M).

% BiliotecaInit
% initial(biliotecaInit).
% dec_p_type(biliotecaInit(libros, info, prestados)).
% biliotecaInit(Libros, Info, Prestados) :-
%     Libros = {} &
%     Info = {} &
%     Prestados = {}.

% #############################################################################

% \begin{schema}{ConsultaOk}
% \Xi Biblioteca \\
% t? : TITULO \\ 
% a? : AUTOR \\
% n!: \nat \\
% \where 
% (t?,a?) \in \ran info \\
% n! = \#(prestados \rres \dom (info \rres \set{(t?,a?)}))) \\
% \end{schema}

% dec_p_type(consultaOk(libros, info, prestados, titulo, autor, {ok, error}, int, libros, info, pretados)).
% consultaOk(Libros, Info, Prestados, T, A, M_o, N_o, Libros_, Info_, Prestados_) :-
%     ran(Info, L) & [T, A] in L &
%     size(M1, N_o) &
%     rres(Prestados, M2, M1) &
%     dom(M3, M2) &
%     rres(Info, {[T,A]}, M3) &
%     M_o = ok &
%     Libros_ = Libros &
%     Info_ = Info &
%     Prestados_ = Prestados.

% #############################################################################

% \begin{schema}{consultaError}
% \Xi Biblioteca \\
% t? : TITULO \\ 
% a? : AUTOR \\
% m! : MSJ
% \where
% (t?,a?) \notin \ran info \\
% m! = error \\
% \end{schema}

% dec_p_type(consultaError(libros, info, prestados, titulo, autor, {ok, error}, libros, info, prestados)).
% consultaError(Libros, Info, Prestados, T, A, M_o, Libros_, Info_, Prestados_) :-
%     ran(Info, L) & [T, A] nin L &
%     M_o = error &
%     Libros_ = Libros &
%     Info_ = Info &
%     Prestados_ = Prestados.

% #############################################################################

% \begin{zed}
% Consulta \defs Consulta \lor consultaError
% \end{zed}

% operation(consulta).
% dec_p_type(consulta(libros, info, prestados, titulo, autor, {ok, error}, int, libros, info, pretados)).
% consulta(Libros, Info, Prestados, T, A, M_o, N_o, Libros_, Info_, Prestados_) :-
%     consultaOk(Libros, Info, Prestados, T, A, M_o, N_o, Libros_, Info_, Prestados_)
%     or
%     consultaError(Libros, Info, Prestados, T, A, M_o, Libros_, Info_, Prestados_).

% #############################################################################

% \begin{schema}{PrestarLibroOk}
% \Delta Biblioteca \\
% l? : ISBN \\ 
% s? : NROSOCIO \\
% m! : MSJ \\
% \where
% s? \notin \dom prestados \\
% l? \in \dom libros \\
% \#(prestados \rres \set{l?}) < libros \# l? \\
% prestados' = prestados \oplus \set{s? \mapsto l?} \\
% libros' = libros \\
% m! = ok \\
% \end{schema}

% dec_p_type(prestarLibroOk(libros, info, prestados, isbn, nrosocio, {ok, error}, libros, info, pretados)).
% prestarLibroOk(Libros, Info, Prestados, L, S, M_o, Libros_, Info_, Prestados_) :-
%     dom(Prestados, A) & S nin A &
%     dom(Libros, B) & L in B &
%     size(C1, N) & rres(Prestados, {L}, C1) & Libros = {[L, M] / C2} & [L, M] nin C2 & N =< M &
%     oplus(Prestados, {[S, L]}, Prestados_) &
%     Libros_ = Libros &
%     Info_ = Info &
%     M_o = ok.

% #############################################################################

% \begin{schema}{SocioExcedeLimite}
% \Xi Biblioteca \\
% s? : NROSOCIO \\
% m! : MSJ \\
% \where
% s? \in \dom prestados \\
% m! = error \\
% \end{schema}

% dec_p_type(socioExcedeLimite(libros, info, prestados, nrosocio, {ok, error}, libros, info, pretados)).
% socioExcedeLimite(Libros, Info, Prestados, S, M_o, Libros_, Info_, Prestados_) :-
%     dom(Prestados, A) & S in A &
%     Prestados_ = Prestados & 
%     Libros_ = Libros &
%     Info_ = Info &
%     M_o = error.

% #############################################################################

% \begin{schema}{LibroNoDisponible}
% \Xi Biblioteca \\
% l? : ISBN \\ 
% m! : MSJ \\
% \where
% \#(prestados \rres \set{l?}) = libros \# l? \\
% m! = error \\
% \end{schema}

% dec_p_type(libroNoDisponible(libros, info, prestados, isbn, {ok, error}, libros, info, pretados)).
% libroNoDisponible(Libros, Info, Prestados, L, M_o, Libros_, Info_, Prestados_) :-
%     dom(Libros, A) & L in A &
%     size(B1, N) & rres(Prestados, {L}, B1) & Libros = {[L, M] / B2} & [L, M] nin B2 & N is M &
%     Prestados_ = Prestados & 
%     Libros_ = Libros &
%     Info_ = Info &
%     M_o = error.

% #############################################################################

% \begin{schema}{LibroNoExiste}
% \Xi Biblioteca \\
% l? : ISBN \\ 
% m! : MSJ \\
% \where
% l? \notin \dom libros \\
% m! = error \\
% \end{schema}

% dec_p_type(libroNoExiste(libros, info, prestados, isbn, {ok, error}, libros, info, pretados)).
% libroNoExiste(Libros, Info, Prestados, L, M_o, Libros_, Info_, Prestados_) :-
%     dom(Libros, A) & L nin A &
%     Prestados_ = Prestados & 
%     Libros_ = Libros &
%     Info_ = Info &
%     M_o = error.

% #############################################################################

% operation(prestarLibro).
% dec_p_type(prestarLibro(libros, info, prestados, isbn, nrosocio, {ok, error}, libros, info, pretados)).
% prestarLibro(Libros, Info, Prestados, L, S, M_o, Libros_, Info_, Prestados_) :-
%     prestarLibroOk(Libros, Info, Prestados, L, S, M_o, Libros_, Info_, Prestados_)
%     or
%     socioExcedeLimite(Libros, Info, Prestados, S, M_o, Libros_, Info_, Prestados_)
%     or
%     libroNoDisponible(Libros, Info, Prestados, L, M_o, Libros_, Info_, Prestados_)
%     or
%     libroNoExiste(Libros, Info, Prestados, L, M_o, Libros_, Info_, Prestados_).

% #############################################################################

% \begin{schema}{DevolverLibroOk}
% \Delta Biblioteca \\
% s? : NROSOCIO \\
% m! : MSJ \\
% \where
% s? \in \dom prestados \\
% prestados' = prestados \dares \set{s?} \\
% m! = ok \\
% \end{schema}

% dec_p_type(devolverLibroOk(libros, info, prestados, nrosocio, {ok, error}, libros, info, pretados)).
% devolverLibroOk(Libros, Info, Prestados, S, M_o, Libros_, Info_, Prestados_) :-
%     dom(Prestados, A) & S in A &
%     dares(Prestados, {S}, Prestados_) &
%     Libros_ = Libros &
%     Info_ = Info &
%     M_o = ok.

% #############################################################################

% \begin{schema}{SocioNoTieneLibroPrestado}
% \Xi Biblioteca \\
% s? : NROSOCIO \\
% m! : MSJ \\
% \where
% s? \notin \dom prestados \\
% m! = error \\
% \end{schema}

% dec_p_type(socioSinLibro(libros, info, prestados, nrosocio, {ok, error}, libros, info, pretados)).
% socioSinLibro(Libros, Info, Prestados, S, M_o, Libros_, Info_, Prestados_) :-
%     dom(Prestados, A) & S nin A &
%     Prestados_ = Prestados & 
%     Libros_ = Libros &
%     Info_ = Info &
%     M_o = error.

% #############################################################################

% \begin{zed}
%     DevolverLibro \defs DevolverLibroOk \lor SocioNoTieneLibroPrestado
% \end{zed}

% operation(devolverLibro).
% dec_p_type(devolverLibro(libros, info, prestados, nrosocio, {ok, error}, libros, info, pretados)).
% devolverLibro(Libros, Info, Prestados, S, M_o, Libros_, Info_, Prestados_) :-
%     devolverLibroOk(Libros, Info, Prestados, S, M_o, Libros_, Info_, Prestados_)
%     or
%     socioSinLibro(Libros, Info, Prestados, S, M_o, Libros_, Info_, Prestados_).

