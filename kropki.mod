param maxDim;                       # MUST be a perfect square
set X := 1..maxDim;                 # x-coordinates
set Y := 1..maxDim;                 # y-coordinates
set N := 1..maxDim;                 # range of numbers each cell can take
set S := 1..maxDim by sqrt(maxDim); # possible top-left coord. of a box
set FIXED within {X,Y,N};           # (x,y) coordinate set

var p{X,Y,N} binary; # binary; denotes if cell at (x,y) coordinate is occupied by number n



# for each row, each number can only appear once
subject to RowCount {x in X, n in N}:
	sum{y in Y} p[x,y,n] = 1;

# for each column, each number can only appear once
subject to ColCount {y in Y, n in N}:
	sum{x in X} p[x,y,n] = 1;

# for each box, each number can only appear once
subject to BoxCount {sx in S, sy in S, n in N}: 
	sum{cx in sx..(sx+sqrt(maxDim)-1)} sum{cy in sy..(sy+sqrt(maxDim)-1)} p[cx,cy,n] = 1;

# each cell can only hold one number
subject to CellAssignment {x in X, y in Y}: 
	sum{n in N} p[x,y,n] = 1;

# fixes initial cell numbers
subject to FixedCells {(x,y,n) in FIXED}:
	p[x,y,n] = 1;