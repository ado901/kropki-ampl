param maxDim; 
param maxNum;                    # la dimensione massima del gioco, nel caso del progetto è 9x9
set N := 1..maxDim;
set NUMERI := 1..maxNum;                 # i numeri ovviamente sono da 1 a 9
set RIQ := 1..maxDim by sqrt(maxDim); # coordinate dei riquadri. essendo il gioco 9x9, i riquadri sono 3x3
set FIXED within {N,N,N};
set BLACKR within {N,N,N};
set BLACKC within {N,N,N};
set WHITER within {N,N,N};
set WHITEC within {N,N,N};

var cella{N,N,NUMERI} binary; # Ogni cella avrà 1 se contiene il numero n, 0 altrimenti

# set dell'istanza proposta
subject to SetIniziale {(x,y,n) in FIXED}:
	cella[x,y,n] = 1;

# esclusività totale delle celle sullo stesso numero
subject to CondizioneCelle {x in N, y in N}: 
	sum{n in N} cella[x,y,n] = 1;



### Vincoli del Sudoku relative alla presenza dei numeri tra righe, colonne e riquadri
subject to Righe {x in N, n in N}:
	sum{y in N} cella[x,y,n] = 1;
subject to Colonne {y in N, n in N}:
	sum{x in N} cella[x,y,n] = 1;
subject to Riquadri {rx in RIQ, ry in RIQ, n in N}: 
	sum{cx in rx..(rx+sqrt(maxDim)-1)} sum{cy in ry..(ry+sqrt(maxDim)-1)} cella[cx,cy,n] = 1;

#le condizioni proposte ora sfruttano la condizione di esclusività delle celle relative allo stesso numero
#condizione consecutiva da sopra a sotto e viceversa. Quando il numero k è minore di 9 e maggiore di 1
subject to BianchiOrizzSu{(j,a,b) in WHITEC, k in N: k + 1 < 10 and k - 1 > 0}:
	cella[b,j,k+1] + cella[b,j,k-1] >= cella[a,j,k];						#allora la cella sotto se quella sopra è occupata da k deve contenere il numero successivo o quello precedente
subject to BianchiOrizzSotto{(j,a,b) in WHITEC, k in N: k + 1 < 10 and k - 1 > 0}:
	cella[a,j,k+1] + cella[a,j,k-1] >= cella[b,j,k];						#allora la cella sopra se quella sotto è occupata da k deve contenere il numero successivo o quello precedente							#allora la cella sopra se quella sotto è occupata da k deve contenere il doppio o la sua metà
#condizione consecutiva da sinistra a destra e viceversa. Quando il numero k è minore di 9 e maggiore di 1
subject to BianchiVerticaliSx{(i,a,b) in WHITER, k in N: k + 1 < 10 and k - 1 > 0}:
	cella[i,b,k+1] + cella[i,b,k-1] >= cella[i,a,k]; 						#allora la cella a destra se quella a sinistra è occupata da k deve contenere il numero successivo o quello precedente
subject to BianchiVerticaliRx{(i,a,b) in WHITER, k in N: k + 1 < 10 and k - 1 > 0}:
	cella[i,a,k+1] + cella[i,a,k-1] >= cella[i,b,k];						#allora la cella a sinistra se quella a destra è occupata da k deve contenere il numero successivo o quello precedente

#condizione doppio da sopra a sotto e viceversa. Quando il numero k è pari e il proprio doppio è minore di 10	
subject to NeriOrizzSu{(j,a,b) in BLACKC, k in N: 2*k < 10 and k/2 - k div 2 = 0}:
	cella[b,j,2*k] + cella[b,j,k/2] >= cella[a,j,k];							#allora la cella sotto se quella sopra è occupata da k deve contenere il doppio o la sua metà
subject to NeriOrizzSotto{(j,a,b) in BLACKC, k in N: 2*k < 10 and k/2 - k div 2 = 0}:
	cella[a,j,2*k] + cella[a,j,k/2] >= cella[b,j,k];
#condizione doppio da sinistra a destra e viceversa. Quando il numero k è pari e il proprio doppio è minore di 10
subject to NeriVerticaliSx{(i,a,b) in BLACKR, k in N: 2*k < 10 and k/2 - k div 2 = 0}:
	cella[i,b,2*k] + cella[i,b,k/2] >= cella[i,a,k];							#allora la cella a destra se quella a sinistra è occupata da k deve contenere il doppio o la sua metà
subject to NeriVerticaliRx{(i,a,b) in BLACKR, k in N: 2*k < 10 and k/2 - k div 2 = 0}:
	cella[i,a,2*k] + cella[i,a,k/2] >= cella[i,b,k]; 							#allora la cella a sinistra se quella a destra è occupata da k deve contenere il doppio o la sua metà



					
