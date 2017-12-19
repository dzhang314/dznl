(* ::Package:: *)

ClearAll[BinaryIndices, BinarySubsets, BinaryDecomposition,
	BitwisePartitions, DualFunctionComponents];

BinaryIndices = Compile[{{n, _Integer}},
	Module[{input = n, output = 0, binaryAddends = Table[0, 0]},
		While[input > 0,
			If[OddQ[input], AppendTo[binaryAddends, output]];
			input = Quotient[input, 2];
			++output];
		binaryAddends]];

BinarySubsets[n_Integer?NonNegative] :=
	1 + BinaryIndices /@ Range[0, 2^n - 1];

BinaryDecomposition = Compile[{{n, _Integer}},
	Module[{input = n, output = 1, binaryAddends = Table[0, 0]},
		While[input > 0,
			If[OddQ[input], AppendTo[binaryAddends, output]];
			input = Quotient[input, 2];
			output = 2 * output];
		binaryAddends]];

BitwisePartitions[0] = {{}};
BitwisePartitions[n_Integer?Positive] :=
	BitwisePartitions[n] = If[EvenQ[n],
		2 * BitwisePartitions[n / 2],
		Join @@ Table[Prepend[j] /@ BitwisePartitions[n - j],
			{j, n - Total /@ Subsets@Rest@BinaryDecomposition[n]}]];

DualFunctionComponents[n_Integer, f_, x_List] /; Length[x] === 2^n :=
	Module[{i, indexList}, Table[
		Sum[Times @@ x[[indexList + 1]] *
				Derivative[Length[indexList]][f]@First[x],
			{indexList, BitwisePartitions[i]}],
		{i, 0, 2^n - 1}]];

DualFunctionComponents[n_Integer, f_, x_] :=
	Module[{i, indexList}, Table[
		Sum[Times @@ Map[Subscript[x, #]&, indexList] *
				Derivative[Length[indexList]][f][Subscript[x, 0]],
			{indexList, BitwisePartitions[i]}],
		{i, 0, 2^n - 1}]];

DualFunctionComponents[n_Integer, k_Integer, f_, x : {_List...}] /;
	Dimensions[x, 2] === {k, 2^n} := Module[{i, tuple, indexList}, Table[
		Sum[Times @@ Extract[x, Transpose[{tuple, indexList + 1}]] *
				Apply[(Derivative @@ Lookup[Counts[tuple], Range[k], 0])[f],
					x[[All, 1]]],
			{indexList, BitwisePartitions[i]},
			{tuple, Tuples[Range[k], Length[indexList]]}],
		{i, 0, 2^n - 1}]];

DualFunctionComponents[n_Integer, k_Integer, f_, x_List] /;
	Length[x] === k := Module[{i, tuple, indexList}, Table[
		Sum[Times @@ MapThread[Subscript[x[[#1]], #2]&, {tuple, indexList}] *
				Apply[(Derivative @@ Lookup[Counts[tuple], Range[k], 0])[f],
					Subscript[x[[#]], 0]& /@ Range[k]],
			{indexList, BitwisePartitions[i]},
			{tuple, Tuples[Range[k], Length[indexList]]}],
		{i, 0, 2^n - 1}]];

DualFunctionComponents[n_Integer, k_Integer, f_, x_] :=
	Module[{i, tuple, indexList}, Table[
		Sum[Times @@ MapThread[Subscript[x, #1, #2]&, {tuple, indexList}] *
				Apply[(Derivative @@ Lookup[Counts[tuple], Range[k], 0])[f],
					Subscript[x, #, 0]& /@ Range[k]],
			{indexList, BitwisePartitions[i]},
			{tuple, Tuples[Range[k], Length[indexList]]}],
		{i, 0, 2^n - 1}]];
