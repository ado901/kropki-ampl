param maxDim;                       # MUST be a perfect square
set X := 1..maxDim;                 # x-coordinates
set Y := 1..maxDim;                 # y-coordinates
set N := 1..maxDim;                 # range of numbers each cell can take
set S := 1..maxDim by sqrt(maxDim); # possible top-left coord. of a box
set FIXED within {X,Y,N};           # (x,y) coordinate set

var cella{X,Y,N} binary; # binary; denotes if cell at (x,y) coordinate is occupied by number n



# for each row, each number can only appear once
subject to Righe {x in X, n in N}:
	sum{y in Y} cella[x,y,n] = 1;

# for each column, each number can only appear once
subject to Colonne {y in Y, n in N}:
	sum{x in X} cella[x,y,n] = 1;

# for each box, each number can only appear once
subject to Riquadri {sx in S, sy in S, n in N}: 
	sum{cx in sx..(sx+sqrt(maxDim)-1)} sum{cy in sy..(sy+sqrt(maxDim)-1)} cella[cx,cy,n] = 1;

# each cell can only hold one number
subject to CondizioneCelle {x in X, y in Y}: 
	sum{n in N} cella[x,y,n] = 1;

# fixes initial cell numbers
subject to FixedCells {(x,y,n) in FIXED}:
	cella[x,y,n] = 1;

subject to BlackRows3{(i,a,b) in BLACKR, k in N: 2*k < 10 and k/2 - k div 2 = 0}:
	cella[i,b,2*k] + cella[i,b,k/2] >= cella[i,a,k];
subject to BlackRowsprova{(i,a,b) in BLACKR, k in N: 2*k < 10 and k/2 - k div 2 = 0}:
	cella[i,a,2*k] + cella[i,a,k/2] >= cella[i,b,k];
	
subject to BlackColumns3{(j,a,b) in BLACKC, k in N: 2*k < 10 and k/2 - k div 2 = 0}:
	cella[b,j,2*k] + cella[b,j,k/2] >= cella[a,j,k];
subject to BlackColumnsprova{(j,a,b) in BLACKC, k in N: 2*k < 10 and k/2 - k div 2 = 0}:
	cella[a,j,2*k] + cella[a,j,k/2] >= cella[b,j,k];
	
subject to WhiteRows3{(i,a,b) in WHITER, k in N: k + 1 < 10 and k - 1 > 0}:
	cella[i,b,k+1] + cella[i,b,k-1] >= cella[i,a,k];
subject to WhiteRowsprova{(i,a,b) in WHITER, k in N: k + 1 < 10 and k - 1 > 0}:
	cella[i,a,k+1] + cella[i,a,k-1] >= cella[i,b,k];

subject to WhiteColums3{(j,a,b) in WHITEC, k in N: k + 1 < 10 and k - 1 > 0}:
	cella[b,j,k+1] + cella[b,j,k-1] >= cella[a,j,k];
subject to WhiteColumsprova{(j,a,b) in WHITEC, k in N: k + 1 < 10 and k - 1 > 0}:
	cella[a,j,k+1] + cella[a,j,k-1] >= cella[b,j,k];