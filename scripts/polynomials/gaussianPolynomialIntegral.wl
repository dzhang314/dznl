(* ::Package:: *)

ClearAll[gD, gDr, u, up, $F, $t, $B];
$RecursionLimit = Infinity;

gD[$F, i_Integer] := $F * $t[i];
gD[$t[i_Integer], j_Integer] := $B[i, j];
gD[$B[i_Integer, j_Integer], k_Integer] := 0;
gD[n_Integer, i_Integer] := 0;

gD[Plus[x_, y__], s_Integer] := Module[{z = {x, y}},
	Plus @@ Map[gD[#, s] &, z]];
gD[Times[x_, y__], s_Integer] := Plus @@ Module[{z = {x, y}},
	Times @@ MapAt[gD[#, s] &, z, #] & /@ Range@Length[z]];
gD[x_ ^ n_Integer, s_Integer] := n * x^(n - 1) * gD[x, s];

gDr[0] = $F;
gDr[n_Integer] := gDr[n] = Expand@gD[gDr[n - 1], n];

u[t_] := t / (1 - t^2);
up[t_] := (1 + t^2) / (1 - t^2)^2;


m = {1, 2, 3};

n = Length[m];
While[True,
	A = RandomReal[{-5, 5}, {n, n}];
	A = With[{U = UpperTriangularize[A]}, Transpose[U] . U];
	If[PositiveDefiniteMatrixQ[A], Break[]]];
s = RandomReal[{-5, 5}, n];
x = Symbol["$x" <> ToString[#]] & /@ Range[n];
expr = Apply[Times, x^m] * Exp[-x.A.x / 2 + s.x];


Join[{expr}, {#, -Infinity, Infinity} & /@ x, {Method -> Automatic}];
NIntegrate @@ %


B = Inverse[A];
t = B.s;
F = Sqrt[(2 * Pi)^n / Det[A]] * Exp[s.t / 2];
indices = Join @@ MapIndexed[ConstantArray[First[#2], #1] &, m];
Fold[gD, $F, indices] /. {
	$F -> F,
	$B[i_, j_] :> B[[i, j]],
	$t[i_] :> t[[i]]
}
