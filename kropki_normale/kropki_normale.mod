param maxDim; 
param maxNum;                    # la dimensione massima del gioco, nel caso del progetto è 9x9
set N := 1..maxDim;
set NUMERI := 1..maxNum;                 # i numeri ovviamente sono da 1 a 9
set RIQ := 1..maxDim by sqrt(maxDim); # coordinate dei riquadri. essendo il gioco 9x9, i riquadri sono 3x3
set FIXED within {N,N,NUMERI};
set NEROR within {N,N,N};
set NEROC within {N,N,N};
set BIANCOR within {N,N,N};
set BIANCOC within {N,N,N};

var cella{N,N,NUMERI} binary; # Ogni cella avrà 1 se contiene il numero n, 0 altrimenti

# set dell'istanza proposta se sono presenti numeri
subject to SetIniziale {(x,y,n) in FIXED}:
	cella[x,y,n] = 1;

# esclusività totale delle celle sullo stesso numero
subject to CondizioneCelle {x in N, y in N}: 
	sum{n in NUMERI} cella[x,y,n] = 1;



### Vincoli del Sudoku relative alla presenza dei numeri tra righe, colonne e riquadri
subject to Righe {x in N, n in N}:
	sum{y in N} cella[x,y,n] = 1;
subject to Colonne {y in N, n in N}:
	sum{x in N} cella[x,y,n] = 1;
subject to Riquadri {rx in RIQ, ry in RIQ, n in N}: 
	sum{cx in rx..(rx+sqrt(maxDim)-1)} sum{cy in ry..(ry+sqrt(maxDim)-1)} cella[cx,cy,n] = 1;

#le condizioni proposte ora sfruttano la condizione di esclusività delle celle relative allo stesso numero
#condizione consecutiva da sopra a sotto e viceversa. Quando il numero k è minore di 9 e maggiore di 1
subject to BianchiOrizzSu{(j,a,b) in BIANCOC, k in NUMERI: k + 1 < maxNum+1 and k - 1 > 0}:
	cella[b,j,k+1] + cella[b,j,k-1] >= cella[a,j,k];
subject to BianchiOrizzSotto{(j,a,b) in BIANCOC, k in NUMERI: k + 1 < maxNum+1 and k - 1 > 0}:
	cella[a,j,k+1] + cella[a,j,k-1] >= cella[b,j,k];
#condizione consecutiva da sinistra a destra e viceversa. Quando il numero k è minore di 9 e maggiore di 1
subject to BianchiVerticaliSx{(i,a,b) in BIANCOR, k in NUMERI: k + 1 < maxNum+1 and k - 1 > 0}:
	cella[i,b,k+1] + cella[i,b,k-1] >= cella[i,a,k];
subject to BianchiVerticaliRx{(i,a,b) in BIANCOR, k in NUMERI: k + 1 < maxNum+1 and k - 1 > 0}:
	cella[i,a,k+1] + cella[i,a,k-1] >= cella[i,b,k];

#VINCOLI PER I NERI
#il pattern è di valutare i numeri sotto la prima metà del range e discriminarli tra pari e dispari
# la stessa cosa è stata fatta anche per i numeri nella seconda metà applicando vincoli diversi a seconda se pari o dispari:
# dispari è la condizione in cui non può mai esserci

subject to NeriColPariPiccoli1{(j,a,b) in NEROC, k in NUMERI: 2*k < maxNum+1 and k mod 2 = 0}:
	cella[b,j,2*k] + cella[b,j,k/2] >= cella[a,j,k];							
subject to NeriColPariPiccoli2{(j,a,b) in NEROC, k in NUMERI: 2*k < maxNum+1 and k mod 2 = 0}:
	cella[a,j,2*k] + cella[a,j,k/2] >= cella[b,j,k];

/* subject to NeriColPariGrandi1{(j,a,b) in NEROC, k in N: 2*k > maxNum+1 and k mod 2 = 0}:
	cella[b,j,k/2] >= cella[a,j,k];
subject to NeriColDispariPiccoli1{(j,a,b) in NEROC, k in N: 2*k < maxNum+1 and k mod 2 != 0}:
	cella[b,j,2*k] >= cella[a,j,k];
subject to NeriColDispariGrandi1{(j,a,b) in NEROC, k in N: 2*k > maxNum+1 and k mod 2 != 0}:
	cella[a,j,k] =0;
subject to NeriColDispariGrandi2{(j,a,b) in NEROC, k in N: 2*k > maxNum+1 and k mod 2 != 0}:
	cella[b,j,k] =0; */



subject to NeriRigaPariPiccoli1{(i,a,b) in NEROR, k in NUMERI: 2*k < maxNum+1 and k mod 2= 0}:
	cella[i,b,2*k] + cella[i,b,k/2] >= cella[i,a,k];							
subject to NeriRigaPariPiccoli2{(i,a,b) in NEROR, k in NUMERI: 2*k < maxNum+1 and k mod 2= 0}:
	cella[i,a,2*k] + cella[i,a,k/2] >= cella[i,b,k]; 

/* subject to NeriRigaPariGrandi2{(i,a,b) in NEROR, k in NUMERI: 2*k > maxNum+1 and k mod 2= 0}:
	cella[i,b,k/2] >= cella[i,a,k];
subject to NeriRigaDispariPiccoli1{(i,a,b) in NEROR, k in NUMERI: 2*k < maxNum+1 and k mod 2 != 0}:
	cella[i,b,2*k] >= cella[i,a,k];
subject to NeriRigaDispariGrandi1{(i,a,b) in NEROR, k in NUMERI: 2*k > maxNum+1 and k mod 2 != 0}:
	cella[i,a,k] = 0;
subject to NeriRigaDispariGrandi2{(i,a,b) in NEROR, k in NUMERI: 2*k > maxNum+1 and k mod 2!= 0}:
	cella[i,b,k] = 0; */

#nessun obiettivo in quanto è un problema CSP


					
