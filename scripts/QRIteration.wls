#!/usr/bin/env wolframscript
(* ::Package:: *)

GrcarMatrix[n_Integer, k_Integer] := ToeplitzMatrix[
	Join[{1, -1}, ConstantArray[0, n - 2]],
	Join[ConstantArray[1, Min[k + 1, n]], ConstantArray[0, Max[n - k - 1, 0]]]];

EmbedMatrix[M_?MatrixQ, i_List, n_Integer] := ReplacePart[IdentityMatrix[n],
	Join @@ Array[({i[[#1]], i[[#2]]} -> M[[#1, #2]])&, Dimensions[M]]];

HessenbergQuadratic[H_?MatrixQ, b_, c_] := With[{t = (H[[1, 1]] + b)}, {
	H[[2, 1]] * H[[1, 2]] + H[[1, 1]] * t + c,
	H[[2, 1]] * (H[[2, 2]] + t),
	H[[2, 1]] * H[[3, 2]]
}];

HouseholderVector[v_?VectorQ] := Normalize@Prepend[Rest[v],
	If[First[v] < 0, First[v] - Norm[v], First[v] + Norm[v]]];


n = 20;
prec = 30;

H = N[GrcarMatrix[n, 3], prec];
reference = Eigenvalues[H];
result = {};

While[n > 2,

	(* Compute shift polynomial p. *)
	tr2Tr = H[[n - 1, n - 1]] + H[[n, n]];
	tr2Det = H[[n - 1, n - 1]] * H[[n, n]] - H[[n - 1, n]] * H[[n, n - 1]];

	(* Compute first column of p(H). *)
	q = HessenbergQuadratic[H, -tr2Tr, tr2Det];

	(* Transform first column, introducing a 3x3 bulge. *)
	v = HouseholderVector[q];
	R = IdentityMatrix@Length[v] - 2 * Outer[Times, v, v];
	Q = EmbedMatrix[R, {1, 2, 3}, n];
	H = SetPrecision[Q . H . Q, prec];

	(* Squeeze the 3x3 bulge down the diagonal. *)
	Do[
		q = H[[i+1 ;; i+3, i]];
		v = HouseholderVector[q];
		R = IdentityMatrix@Length[v] - 2 * Outer[Times, v, v];
		Q = EmbedMatrix[R, {i+1, i+2, i+3}, n];
		H = SetPrecision[Q . H . Q, prec],
		{i, n - 3}
	];

	(* Eliminate the final 2x2 bulge. *)
	q = H[[n-1 ;; n, n-2]];
	v = HouseholderVector[q];
	R = IdentityMatrix@Length[v] - 2 * Outer[Times, v, v];
	Q = EmbedMatrix[R, {n-1, n}, n];
	H = SetPrecision[Q . H . Q, prec];

	If[Abs@H[[n-1, n-2]] < 10^-prec * (Abs@H[[n-1, n-1]] + Abs@H[[n-2, n-2]]),
		result = Join[result, Eigenvalues[H[[n-1 ;; n, n-1 ;; n]]]];
		H = H[[1 ;; n-2, 1 ;; n-2]];
		n -= 2]];

result = Join[result, Eigenvalues[H]];
