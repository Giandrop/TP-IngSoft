# TP-IngSoft

Ejecutamos el check_vcs de biblioteca

{log}=> check_vcs_biblioteca.

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

Total VCs: 11 (discharged: 10, failed: 1, timeout: 0)
Execution time (excluding timeouts): 0.580756425857544 s
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

{log}=> check_vcs_biblioteca.

Checking altaLibro_pi_invTipo ... OK

Total VCs: 1 (discharged: 1, failed: 0, timeout: 0)
Execution time (excluding timeouts): 0.06345748901367188 s
yes