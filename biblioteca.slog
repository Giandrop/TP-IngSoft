% Variables de estado
variables([Libros, CantPrestada, Prestamos]).

% Tipo MSJ
def_type(msj, enum([ok, no_existe, no_disponible, excede_limite])).

% parameters([Datos]).
% axiom(datos_pf).
% decp_p_type(datos_pf(isbn, cp(titulo, autor))).
% datos_pf(Datos) :- pfun(Datos).

% Sinónimos de tipos para cada una de las variables
def_type(libros, rel(isbn, int)).
def_type(cantPrestada, rel(isbn, int)).
def_type(prestamos, rel(nrosocio, isbn)).

% #############################################################################

% Invariantes de tipos
invariant(invTipo).
dec_p_type(invTipo(libros, cantPrestada, prestamos)).
invTipo(Libros, CantPrestada, Prestamos) :-
    pfun(Libros) &
    pfun(CantPrestada) &
    pfun(Prestamos).

% Invariante de estado
invariant(bibliotecaInv).
dec_p_type(bibliotecaInv(cantPrestada, libros)).
bibliotecaInv(CantPrestada, Libros) :-
    % dec_type(A, set(isbn)) &
    % dom(CantPrestada, A) & dom(Libros, B) & A = B.
    let([A, B], dom(CantPrestada, A) & dom(Libros, B), A = B).

% #############################################################################

% BibliotecaInit
initial(bibliotecaInit).
dec_p_type(bibliotecaInit(libros, cantPrestada, prestamos)).
bibliotecaInit(Libros, CantPrestada, Prestamos) :-
    Libros = {} &
    CantPrestada = {} &
    Prestamos = {}.

% #############################################################################

% Operación: AltaLibro

dec_p_type(altaLibroNuevo(libros, cantPrestada, prestamos, isbn, int, libros, cantPrestada, prestamos)).
altaLibroNuevo(Libros, CantPrestada, Prestamos, L, N, Libros_, CantPrestada_, Prestamos_) :-
    dec(DomLibros, set(isbn)) & dom(Libros, DomLibros) & L nin DomLibros
    & N >= 0
    & un(Libros, {[L, N]}, Libros_)
    & un(CantPrestada, {[L, 0]}, CantPrestada_)
    & Prestamos_ = Prestamos.

dec_p_type(altaLibroExistente(libros, cantPrestada, prestamos, isbn, int, libros, cantPrestada, prestamos)).
altaLibroExistente(Libros, CantPrestada, Prestamos, L, N, Libros_, CantPrestada_, Prestamos_) :-
    dec(DomLibros, set(isbn)) & dom(Libros, DomLibros) & L in DomLibros
    & N >= 0
    & dec([Cant1, Cant2], int) & applyTo(Libros, L, Cant1) & Cant2 is N + Cant1 & oplus(Libros, {[L, Cant2]}, Libros_)
    & CantPrestada_ = CantPrestada
    & Prestamos_ = Prestamos.

operation(altaLibro).
dec_p_type(altaLibro(libros, cantPrestada, prestamos, isbn, int, libros, cantPrestada, prestamos)).
altaLibro(Libros, CantPrestada, Prestamos, L, N, Libros_, CantPrestada_, Prestamos_) :- 
    altaLibroNuevo(Libros, CantPrestada, Prestamos, L, N, Libros_, CantPrestada_, Prestamos_)
    or
    altaLibroExistente(Libros, CantPrestada, Prestamos, L, N, Libros_, CantPrestada_, Prestamos_).

% #############################################################################

% Operación: consultarLibro

dec_p_type(consultarLibroOk(libros, cantPrestada, prestamos, isbn, int, msj)).
consultarLibroOk(Libros, CantPrestada, Prestamos, L, N, M) :-
    dec(DomLibros, set(isbn)) & dom(Libros, DomLibros) & L in DomLibros
    & dec([Cant1, Cant2], int) & applyTo(CantPrestada, L, Cant1) & applyTo(Libros, L, Cant2) & Cant1 < Cant2
    & N is Cant2 - Cant1
    & M = ok.

dec_p_type(consultarLibroNoDisponible(libros, cantPrestada, prestamos, isbn, msj)).
consultarLibroNoDisponible(Libros, CantPrestada, Prestamos, L, M) :-
    dec(DomLibros, set(isbn)) & dom(Libros, DomLibros) & L in DomLibros
    & dec([Cant1, Cant2], int) & applyTo(CantPrestada, L, Cant1) & applyTo(Libros, L, Cant2) & Cant1 = Cant2
    & M = no_disponible.

dec_p_type(libroNoExiste(libros, cantPrestada, prestamos, isbn, msj)).
libroNoExiste(Libros, CantPrestada, Prestamos, L, M) :-
    dec(DomLibros, set(isbn)) & dom(Libros, DomLibros) & L nin DomLibros
    & M = no_existe.

operation(consultarLibro).
dec_p_type(consultarLibro(libros, cantPrestada, prestamos, isbn, int, msj)).
consultarLibro(Libros, CantPrestada, Prestamos, L, N, M) :-
    consultarLibroOk(Libros, CantPrestada, Prestamos, L, N, M)
    or
    consultarLibroNoDisponible(Libros, CantPrestada, Prestamos, L, M)
    or
    libroNoExiste(Libros, CantPrestada, Prestamos, L, M).

% #############################################################################

% Operación: PrestarLibro

dec_p_type(prestarLibroOk(libros, cantPrestada, prestamos, isbn, nrosocio, msj, libros, cantPrestada, prestamos)).
prestarLibroOk(Libros, CantPrestada, Prestamos, L, S, M, Libros_, CantPrestada_, Prestamos_) :-
    dec(DomPrestamos, set(nrosocio)) & dom(Prestamos, DomPrestamos) & S nin DomPrestamos
    & dec(DomLibros, set(isbn)) & dom(Libros, DomLibros) & L in DomLibros
    & dec([Cant1, Cant2], int) & applyTo(CantPrestada, L, Cant1) & applyTo(Libros, L, Cant2) & Cant1 < Cant2
    & Libros_ = Libros
    & dec([C, Cplus1], int) & applyTo(CantPrestada, L, C) & Cplus1 is C + 1 & oplus(CantPrestada, {[L, Cplus1]}, CantPrestada_)
    & oplus(Prestamos, {[S, L]}, Prestamos_)
    & M = ok.

dec_p_type(socioExcedeLimite(libros, cantPrestada, prestamos, nrosocio, msj)).
socioExcedeLimite(Libros, CantPrestada, Prestamos, S, M) :-
    dec(DomPrestamos, set(nrosocio)) & dom(Prestamos, DomPrestamos) & S in DomPrestamos
    & M = excede_limite.

dec_p_type(libroNoDisponible(libros, cantPrestada, prestamos, isbn, msj)).
libroNoDisponible(Libros, CantPrestada, Prestamos, L, M) :-
    dec(DomLibros, set(isbn)) & dom(Libros, DomLibros) & L in DomLibros
    & dec([Cant1, Cant2], int) & applyTo(CantPrestada, L, Cant1) & applyTo(Libros, L, Cant2) & Cant1 = Cant2
    & M = no_disponible.

operation(prestarLibro).
dec_p_type(prestarLibro(libros, cantPrestada, prestamos, isbn, nrosocio, msj, libros, cantPrestada, prestamos)).
prestarLibro(Libros, CantPrestada, Prestamos, L, S, M, Libros_, CantPrestada_, Prestamos_) :-
    prestarLibroOk(Libros, CantPrestada, Prestamos, L, S, M, Libros_, CantPrestada_, Prestamos_)
    or ((socioExcedeLimite(Libros, CantPrestada, Prestamos, S, M) 
        or libroNoDisponible(Libros, CantPrestada, Prestamos, L, M))
        & Libros_ = Libros & CantPrestada_ = CantPrestada & Prestamos_ = Prestamos).

