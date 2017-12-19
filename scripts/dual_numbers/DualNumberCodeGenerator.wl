(* ::Package:: *)

ClearAll[dualComponentNames, dualTypeName, dualStructDeclaration,
	dualAddDefinition, dualSubDefinition, dualMulDefinition,
	termList, signPair, dualDivDefinition];

dualComponentNames[n_Integer?NonNegative] :=
	Prepend["dual" <> StringJoin[ToString /@ #]& /@ Rest@BinarySubsets[n], "real"];

dualTypeName[n_Integer?NonNegative] := "hyperdual" <> ToString[n] <> "_t";

dualStructDeclaration[n_Integer?NonNegative] := Join[
	{TemplateApply["struct dual``_t {\n", n]},
	StringTemplate["    double ``;\n"] /@ dualComponentNames[n],
	{"};\n"}];

dualAddDefinition[n_Integer?NonNegative] := Join[
	{TemplateApply[
			"`1` operator+(const `1` &x, const `1` &y) {\n",
			dualTypeName[n]],
		"    return {\n"},
	StringTemplate["        .`1` = x.`1` + y.`1`,\n"] /@ dualComponentNames[n],
	{"    };\n", "}\n"}];

dualSubDefinition[n_Integer?NonNegative] := Join[
	{TemplateApply[
			"`1` operator-(const `1` &x, const `1` &y) {\n",
			dualTypeName[n]],
		"    return {\n"},
	StringTemplate["        .`1` = x.`1` - y.`1`,\n"] /@ dualComponentNames[n],
	{"    };\n", "}\n"}];

dualMulDefinition[n_Integer?NonNegative] := Join[
	{TemplateApply[
			"`1` operator*(const `1` &x, const `1` &y) {\n",
			dualTypeName[n]],
		"    return {\n"},
	MapThread[StringTemplate["        .`` = ``,\n"], {
		dualComponentNames[n], Activate[
			DualFunctionComponents[n, 2, Times, {\[FormalX], \[FormalY]}] /. {
				Times -> (Inactive[StringJoin] @@ Riffle[{##}, " * "]&),
				Plus -> (Inactive[StringJoin] @@ Riffle[{##}, " + "]&)} /. Join[
				Thread@Rule[Subscript[\[FormalX],#]&/@Range[0,2^n-1],
					StringTemplate["x.``"]/@dualComponentNames[n]],
				Thread@Rule[Subscript[\[FormalY],#]&/@Range[0,2^n-1],
					StringTemplate["y.``"]/@dualComponentNames[n]]]]}],
	{"    };\n", "}\n"}];

termList[expr_] := If[Head[expr] === Plus, List @@ expr, {expr}, {expr}];

signPair[expr_] := If[Head[expr] === Times,
	If[AnyTrue[expr, NumericQ[#] && Negative[#]&],
		{Minus, List @@ Minus[expr]},
		{Plus, List @@ expr},
		{Plus, List @@ expr}],
	{Plus, {expr}},
	{Plus, {expr}}];

dualDivDefinition[n_Integer?NonNegative] := Block[
	{temporaryVariableTemplate, temporaryVariableDeclarations,
		quotientPolynomials, quotientExpressions},
	temporaryVariableTemplate = StringTemplate["    const auto `` = `` / " <>
		"y." <> First@dualComponentNames[n] <> ";\n"];
	temporaryVariableDeclarations = Join[
		MapThread[temporaryVariableTemplate,
			{"u" <> StringJoin[ToString /@ #]& /@ BinarySubsets[n],
				StringTemplate["x.``"] /@ dualComponentNames[n]}],
		MapThread[temporaryVariableTemplate,
			{"v" <> StringJoin[ToString /@ #]& /@ Rest@BinarySubsets[n],
				StringTemplate["y.``"] /@ Rest@dualComponentNames[n]}]];
	quotientPolynomials = DualFunctionComponents[
		n, 2, Divide, {\[FormalX], \[FormalY]}] /. Join[
			Thread@Rule[Thread[Subscript[\[FormalX], #]& /@ Range[0, 2^n - 1]],
				Subscript[\[FormalY], 0] * \[FormalU][#]& /@ Range[0, 2^n - 1]],
			Thread@Rule[Thread[Subscript[\[FormalY], #]& /@ Range[2^n - 1]],
				Subscript[\[FormalY], 0] * \[FormalV][#]& /@ Range[2^n-1]]];
	quotientExpressions = Table[Block[{
		termPairs = MapAt[StringJoin@Riffle[#, " * "]&,
			MapAt[Switch[Head[#],
					Integer, ToString[#],
					\[FormalU], "u" <> StringJoin[ToString /@
						(1 + BinaryIndices@First[#])],
					\[FormalV], "v" <> StringJoin[ToString /@
						(1 + BinaryIndices@First[#])]]&,
				signPair /@ termList[expr],
				{All, 2, All}],
			{All, 2}]},
		StringJoin@Riffle[
			MapIndexed[If[#2 === {1},
					Switch[#1, Plus, "", Minus, "-"],
					Switch[#1, Plus, " + ", Minus, " - "],
					Switch[#1, Plus, " + ", Minus, " - "]]&,
				termPairs[[All, 1]]],
			termPairs[[All, 2]]]],
		{expr, quotientPolynomials}];
	Join[
		{TemplateApply[
			"`1` operator/(const `1` &x, const `1` &y) {\n",
			dualTypeName[n]]},
		temporaryVariableDeclarations,
		{"    return {\n"},
		MapThread[StringTemplate["        .`` = ``,\n"],
			{dualComponentNames[n], quotientExpressions}],
		{"    };\n", "}\n"}]];
