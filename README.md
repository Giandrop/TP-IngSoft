# TP-IngSoft

type_check.
add_lib("osets.slog").
consult("biblioteca.slog").

Descargamos las condiciones de verificación
```
{log}=> vcg("biblioteca.slog").

yes
```

Las cargamos

```
{log}=> consult("biblioteca-vc.slog").
...
file biblioteca-vc.slog consulted.

yes
```


reset_types.
type_check.
add_lib("osets.slog").
consult("biblioteca_datos.slog").

Ejecutamos el check_vcs de biblioteca

{log}=> check_vcs_biblioteca.

Checking axioms_sat ... OK
Checking bibliotecaInit_sat_invTipo ... OK
Checking bibliotecaInit_sat_bibliotecaInv ... OK
Checking altaLibro_is_sat ... OK
Checking consultarLibro_is_sat ... OK
Checking prestarLibro_is_sat ... OK
Checking altaLibro_pi_invTipo ... ERROR
Checking altaLibro_pi_bibliotecaInv ... OK
Checking consultarLibro_pi_invTipo ... OK
Checking consultarLibro_pi_bibliotecaInv ... OK
Checking prestarLibro_pi_invTipo ... OK
Checking prestarLibro_pi_bibliotecaInv ... OK

Total VCs: 12 (discharged: 11, failed: 1, timeout: 0)
Execution time (excluding timeouts): 3.8401384353637695 s
yes

Vemos que altaLibro_pi_invTipo nos da ERROR, chequeamos un contraejemplo

{log}=> vcgce(altaLibro_pi_invTipo).

Libros = {},  
CantPrestada = {[n1,n0]},  
Prestamos = {},  
L = n1,  
N = 0,  
Libros_ = {[n1,0]},  
CantPrestada_ = {[n1,0],[n1,n0]},  
Prestamos_ = {}

yes

Vemos que la invariante no se cumple porque parte del estado donde n1 no está en el dominio
de Libros pero si en el dominio de CantPrestada, esta situación no pasaría si se cumple la
invariante bibliotecaInv.

Agregamos esta hipótesis al lema de invariante que falla

altaLibro_pi_invTipo(Libros,CantPrestada,Prestamos,Libros,CantPrestada,Prestamos,L,N,Libros_,CantPrestada_,Prestamos_) :-
  bibliotecaInv(CantPrestada, Libros) & 
  neg(
    invTipo(Libros,CantPrestada,Prestamos) &
    altaLibro(Libros,CantPrestada,Prestamos,L,N,Libros_,CantPrestada_,Prestamos_) implies
    invTipo(Libros_,CantPrestada_,Prestamos_)
  ).

Y volvemos a chequear:

{log}=> consult("biblioteca-vc.slog").
{log}=> check_vcs_biblioteca.

Checking altaLibro_pi_invTipo ... OK

Total VCs: 1 (discharged: 1, failed: 0, timeout: 0)
Execution time (excluding timeouts): 0.06345748901367188 s
yes

---
Versión con secuencias:
{log}=> check_vcs_biblioteca_seq.

Checking axioms_sat ... OK
Checking bibliotecaInit_sat_invTipo ... OK
Checking bibliotecaInit_sat_bibliotecaInv ... OK
Checking altaLibro_is_sat ... OK
Checking consultarLibro_is_sat ... OK
Checking prestarLibro_is_sat ... OK
Checking altaLibro_pi_invTipo ... OK
Checking altaLibro_pi_bibliotecaInv ... OK
Checking consultarLibro_pi_invTipo ... OK
Checking consultarLibro_pi_bibliotecaInv ... OK
Checking prestarLibro_pi_invTipo ... OK
Checking prestarLibro_pi_bibliotecaInv ... TIMEOUT

Total VCs: 12 (discharged: 11, failed: 0, timeout: 1)
Execution time (excluding timeouts): 16.007385969161987 s
yes

{log}=> check_vcs_biblioteca_seq(2000, try(prover_all)).

Checking prestarLibro_pi_bibliotecaInv ... OK

Total VCs: 1 (discharged: 1, failed: 0, timeout: 0)
Execution time (excluding timeouts): 58.145206928253174 s
yes

@TODO: chequear con:
check_vcs_biblioteca_seq(2000, [oplus_fe]).

check_vcs_biblioteca_datos(2000, [oplus_fe]).


---
Corremos las simulaciones:




consult("biblioteca.slog").
vcg("biblioteca.slog").
consult("biblioteca-vc.slog").
check_vcs_biblioteca.

---
ttf(biblioteca).

Comenzamos haciendo DNF de alta libro
applydnf(altaLibro(L,N)).

Vemos que nos genera dos ramas:
```
{log}=> writett.

altaLibro_vis
  altaLibro_dnf_1
  altaLibro_dnf_2

yes
```

Guardamos el archivo:
```
{log}=> exporttt.
ttf: testing tree successfully exported to biblioteca_altaLibro-tt.slog

yes
```

Vemos los resultados:
```
altaLibro_dnf_1(L,N,Libros,CantPrestada,Prestamos) :-
  N>=0 &
  L nin _5400 &
  dom(Libros,_5400) &
  dec(_5400,set(isbn)).

altaLibro_dnf_2(L,N,Libros,CantPrestada,Prestamos) :-
  _5598 is N+_5694 &
  applyTo(Libros,L,_5694) &
  dec([_5694,_5598],int) &
  N>=0 &
  L in _5620 &
  dom(Libros,_5620) &
  dec(_5620,set(isbn)).
```

Vemos que el primer caso corresponde al escenario donde L no pertenece al dominio de Libros. Que corresponde al predicado altaLibroNuevo
Mientras que en el segundo caso L si pertenece al 
dominio de Libros

En la primera operación tenemos dos uniones:
& un(Libros, {[L, N]}, Libros_)
& un(CantPrestada, {[L, 0]}, CantPrestada_)

En la segunda tenemos un oplus:
oplus(Libros, {[L, Cant2]}, Libros_)

Aplicamos sp sobre la primera
applysp(altaLibro_dnf_1, un(Libros, {[L, N]}, Libros_)).

altaLibro_vis
  altaLibro_dnf_1
    altaLibro_sp_11
    altaLibro_sp_12
    altaLibro_sp_13
    altaLibro_sp_14
    altaLibro_sp_15
    altaLibro_sp_16
    altaLibro_sp_17
    altaLibro_sp_18
  altaLibro_dnf_2

yes

Tenemos 8 casos de pruebas nuevos, cada uno correspondiente
a un elemento de la partición estandar

Vemos que la clase de prueba altaLibro_sp_11
tiene {[L,N]}={} en su definición.
```
altaLibro_sp_11(L,N,Libros,CantPrestada,Prestamos) :-
  N>=0 &
  L nin _5504 &
  dom(Libros,_5504) &
  dec(_5504,set(isbn)) &
  Libros={} &
  {[L,N]}={}.
```
Esto la hace insatisfacible.

Hacemos prunett para podar esta y otras clases de pruebas insatisfacibles.

```
{log}=> prunett.
                                                                        
yes

{log}=> writett.

altaLibro_vis
  altaLibro_dnf_1
    altaLibro_sp_12
    altaLibro_sp_14
  altaLibro_dnf_2
    altaLibro_sp_24
    altaLibro_sp_25
    
yes
```

applyii(altaLibro_sp_25, N, [1]).
prunett.


Generamos los casos de prueba:
{log}=> gentc.
                  
yes


