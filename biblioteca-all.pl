dinvariant(bibliotecaInv,bibliotecaInv(Libros,Prestados)).
all_unsat_vc(consulta_pi_bibliotecaInv,inv,bibliotecaInv,consulta_pi_bibliotecaInv(Libros,Prestados,Libros,Info,Prestados,T,A,M_o,N_o,Libros_,Info_,Prestados_),consulta(Libros,Info,Prestados,T,A,M_o,N_o,Libros_,Info_,Prestados_)).
all_unsat_vc(prestarLibro_pi_bibliotecaInv,inv,bibliotecaInv,prestarLibro_pi_bibliotecaInv(Libros,Prestados,Libros,Info,Prestados,L,S,M_o,Libros_,Info_,Prestados_),prestarLibro(Libros,Info,Prestados,L,S,M_o,Libros_,Info_,Prestados_)).
all_unsat_vc(devolverLibro_pi_bibliotecaInv,inv,bibliotecaInv,devolverLibro_pi_bibliotecaInv(Libros,Prestados,Libros,Info,Prestados,S,M_o,Libros_,Info_,Prestados_),devolverLibro(Libros,Info,Prestados,S,M_o,Libros_,Info_,Prestados_)).
