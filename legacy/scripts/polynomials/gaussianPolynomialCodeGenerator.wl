(* ::Package:: *)

Needs["CCodeGenerator`"];

ClearAll[gDi, temp, tempCount, $t, $B, $temp];

tempCount = 0;
gDi[{}] = 1;

gDi[{i_}] := Module[{expr = $t[i]},
	temp[++tempCount] = expr;
	gDi[{i}] = $temp[tempCount]];

gDi[is_List] := Module[{expr =
	gDi[is[[;; -2]]] * $t[is[[-1]]] +
		gDi[is[[;; -3]]] * $B[is[[-2]], is[[-1]]] +
		Dot[gDi@Delete[Most[is], #] & /@ Range[Length[is] - 2],
			$B[#, is[[-1]]] & /@ is[[;; -3]]]},
	temp[++tempCount] = expr;
	gDi[is] = $temp[tempCount]];

tempIndices = Table[
	gDi[CArray["indices", #] & /@ Range[0, n - 1]];
	tempCount,
	{n, 0, 20}];

tempExpr[n_Integer] := temp[n] //. {
	$t[i_] :> CArray["t", i],
	$B[i_, j_] :> CArray["B", {i, j}],
	$temp[i_] :> "temp" <> ToString[i]
} //. {
	Plus[Times[a_, b_], c_] :> CCall["std::fma", {a, b, c}]
} //. {
	Plus[arg_, args__] :> COperator[Plus, {arg, args}],
	Times[arg_, args__] :> COperator[Times, {arg, args}]
};

tempDefinition[n_Integer] := CDeclare["double",
	CAssign["temp" <> ToString[n], tempExpr[n]]];

definitionBlocks = Map[tempDefinition] /@ Range @@@ Transpose[{
	Most[tempIndices] + 1, Rest[tempIndices]}];

tempReturns = MapIndexed[CIf[
	COperator[Equal, {"indices.size()", First[#2] - 1}],
	CReturn["temp" <> ToString[#1]]] &, tempIndices];

Export["gaussianIntegral.c",
	ToCCodeString@Flatten@Riffle[tempReturns, definitionBlocks],
	"Text"];
