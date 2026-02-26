% Variables de estado
variables([Libros, CantPrestada, Prestamos]).

% Tipo MSJ
def_type(msj, enum([ok, error])).

parameters([Datos]).
axiom(datos_pf).
decp_p_type(datos_pf(isbn, cp(titulo, autor))).
datos_pf(Datos) :- pfun(Datos).

% Sinónimos de tipos para cada una de las variables
def_type(libros, rel(isbn, int)).
def_type(cantPrestada, rel(isbn, int)).
def_type(prestamos, rel(nrosocio, isbn)).

% #############################################################################

% BiliotecaInit
initial(biliotecaInit).
dec_p_type(biliotecaInit(libros, cantPrestada, prestamos)).
biliotecaInit(Libros, CantPrestada, Prestamos) :-
    Libros = {} &
    CantPrestada = {} &
    Prestamos = {}.

% #############################################################################

% Invariantes de tipos
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

% Operación: ConsultaDisponibilidad

dec_p_type(consultaDisponibilidadOk(libros, cantPrestada, prestamos, isbn, int, msj)).
consultaDisponibilidadOk(Libros, CantPrestada, Prestamos, L, N, M) :-
    dec(DomLibros, set(isbn)) & dom(Libros, DomLibros) & L in DomLibros
    & dec([Cant1, Cant2], int) & applyTo(CantPrestada, L, Cant1) & applyTo(Libros, L, Cant2) & Cant1 =< Cant2
    & N is Cant2 - Cant1
    & M = ok.

dec_p_type(libroNoExiste(libros, cantPrestada, prestamos, isbn, msj)).
libroNoExiste(Libros, CantPrestada, Prestamos, L, M) :-
    dec(DomLibros, set(isbn)) & dom(Libros, DomLibros) & L nin DomLibros
    & M = error.

operation(consultaDisponibilidad).
dec_p_type(consultaDisponibilidad(libros, cantPrestada, prestamos, isbn, int, msj)).
consultaDisponibilidad(Libros, CantPrestada, Prestamos, L, N, M) :-
    consultaDisponibilidadOk(Libros, CantPrestada, Prestamos, L, N, M)
    or
    libroNoExiste(Libros, CantPrestada, Prestamos, L, M).

% #############################################################################

% Operación: PrestarLibro

dec_p_type(prestarLibroOk(libros, cantPrestada, prestamos, isbn, nrosocio, msj, libros, cantPrestada, prestamos)).
prestarLibroOk(Libros, CantPrestada, Prestamos, L, S, M, Libros_, CantPrestada_, Prestamos_) :-
    dec(DomPrestamos, set(nrosocio)) & S nin DomPrestamos
    & dec(DomLibros, set(isbn)) & L in DomLibros
    & dec([Cant1, Cant2], int) & applyTo(CantPrestada, L, Cant1) & applyTo(Libros, L, Cant2) & Cant1 =< Cant2
    & Libros_ = Libros
    & dec([C, Cplus1], int) & applyTo(CantPrestada, L, C) & Cplus1 is C + 1 & oplus(CantPrestada, {[L, Cplus1]}, CantPrestada_)
    & oplus(Prestamos, {[S, L]}, Prestamos_)
    & M = ok.

dec_p_type(socioExcedeLimite(libros, cantPrestada, prestamos, nrosocio, msj)).
socioExcedeLimite(Libros, CantPrestada, Prestamos, S, M) :-
    dec(DomPrestamos, set(nrosocio)) & S in DomPrestamos
    & M = error.

dec_p_type(libroNoDisponible(libros, cantPrestada, prestamos, isbn, msj)).
libroNoDisponible(Libros, CantPrestada, Prestamos, L, M) :-
    dec(DomLibros, set(isbn)) & L in DomLibros
    & dec([Cant1, Cant2], int) & applyTo(CantPrestada, L, Cant1) & applyTo(Libros, L, Cant2) & Cant1 = Cant2
    & M = error.

operation(prestarLibro).
dec_p_type(prestarLibro(libros, cantPrestada, prestamos, isbn, nrosocio, msj, libros, cantPrestada, prestamos)).
prestarLibro(Libros, CantPrestada, Prestamos, L, S, M, Libros_, CantPrestada_, Prestamos_) :-
    prestarLibroOk(Libros, CantPrestada, Prestamos, L, S, M, Libros_, CantPrestada_, Prestamos_)
    or ((socioExcedeLimite(Libros, CantPrestada, Prestamos, S, M) 
        or libroNoDisponible(Libros, CantPrestada, Prestamos, L, M))
        & Libros_ = Libros & CantPrestada_ = CantPrestada & Prestamos_ = Prestamos).

