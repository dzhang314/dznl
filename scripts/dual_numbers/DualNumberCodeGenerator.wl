(* ::Package:: *)

ClearAll[dualComponentNames, dualTypeName, dualStructDefinition,
	dualPosDefinition, dualNegDefinition,
	dualAddDefinition, dualSubDefinition,
	dualMulDefinition,
	termList, signPair, dualDivDefinition];

dualComponentNames[0] := {"real"};
dualComponentNames[1] := {"real", "dual"};
dualComponentNames[n_Integer?NonNegative] := Prepend[
	"dual" <> StringJoin[ToString /@ #]& /@ Rest@BinarySubsets[n],
	"real"];

dualTypeName[0] := "real";
dualTypeName[1] := "dual";
dualTypeName[2] := "hyperdual";
dualTypeName[n_Integer?NonNegative] := "hyperdual" <> ToString[n];

dualStructDefinition[n_Integer?NonNegative] := {
	TemplateApply["struct `` {\n", dualTypeName[n]],
	TemplateApply["    double ``;\n",
		StringJoin@Riffle[dualComponentNames[n], ", "]],
	"};\n"};

dualPosDefinition[n_Integer?NonNegative] := Join[
	{TemplateApply[
			"`1` operator+(const `1` &x) {\n",
			dualTypeName[n]],
		"    return {\n"},
	StringTemplate["        .`1` = +x.`1`,\n"] /@ dualComponentNames[n],
	{"    };\n", "}\n"}];

dualNegDefinition[n_Integer?NonNegative] := Join[
	{TemplateApply[
			"`1` operator-(const `1` &x) {\n",
			dualTypeName[n]],
		"    return {\n"},
	StringTemplate["        .`1` = -x.`1`,\n"] /@ dualComponentNames[n],
	{"    };\n", "}\n"}];

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
				Thread@Rule[Subscript[\[FormalX], #]& /@ Range[0, 2^n - 1],
					StringTemplate["x.``"] /@ dualComponentNames[n]],
				Thread@Rule[Subscript[\[FormalY], #]& /@ Range[0, 2^n - 1],
					StringTemplate["y.``"] /@ dualComponentNames[n]]]]}],
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
			Thread@Rule[Thread@Subscript[\[FormalX], Range[0, 2^n - 1]],
				Subscript[\[FormalY], 0] * Thread@\[FormalU]@Range[0, 2^n - 1]],
			Thread@Rule[Thread@Subscript[\[FormalY], Range[2^n - 1]],
				Subscript[\[FormalY], 0] * Thread@\[FormalV]@Range[2^n - 1]]];
	quotientExpressions = Table[Block[{
		termPairs = MapAt[StringJoin@Riffle[#, " * "]&,
			MapAt[Switch[Head[#],
					Integer, ToString[#] <> ".0",
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

dualExpDefinition[n_Integer?NonNegative] := Block[
	{exponentialPolynomials, temporaryVariables,
		temporaryCounts, temporaryGroups,
		necessaryTemporaries, unnecessaryTemporaries,
		variableNameRules, temporaryVariableDeclarations,
		exponentialExpressions},
	exponentialPolynomials = Expand[
		Rest@DualFunctionComponents[n, Exp, \[FormalX]] /
			Exp@Subscript[\[FormalX], 0]];
	temporaryVariables = {};
	While[True, With[
		{t = FirstCase[exponentialPolynomials, Times[_, __], Null, All]},
		If[t === Null, Break[]];
		AppendTo[temporaryVariables, t];
		exponentialPolynomials = exponentialPolynomials /.
			t -> \[FormalT]@Length[temporaryVariables]]];
	temporaryCounts = Counts@Cases[
		{exponentialPolynomials, temporaryVariables}, _\[FormalT], All];
	temporaryGroups = GroupBy[
		\[FormalT] /@ Range@Length[temporaryVariables],
		GreaterThan[1] @* temporaryCounts];
	necessaryTemporaries = Lookup[temporaryGroups, True, {}];
	unnecessaryTemporaries = Lookup[temporaryGroups, False, {}];
	exponentialPolynomials = exponentialPolynomials /. Thread@Rule[
		unnecessaryTemporaries,
		Extract[temporaryVariables, List @@@ unnecessaryTemporaries]];
	variableNameRules = Join[
		Thread@Rule[Subscript[\[FormalX], #]& /@ Range[0, 2^n - 1],
			StringTemplate["x.``"] /@ dualComponentNames[n]],
		Thread@Rule[necessaryTemporaries,
			StringTemplate["t``"] @@@ necessaryTemporaries]];
	temporaryVariableDeclarations = MapThread[
		StringTemplate["    const auto `` = ``;\n"], {
		StringTemplate["t``"] @@@ necessaryTemporaries,
		Map[StringJoin@Riffle[#, " * "]&,
			List @@@ Extract[temporaryVariables,
				List @@@ necessaryTemporaries] /. variableNameRules]}];
	exponentialExpressions = Map[
		"t0 * (" <> StringJoin@Riffle[#, " + "] <> ")"&,
		termList /@ exponentialPolynomials /.
			Times -> Inactive[Times] /.
			variableNameRules /.
			Inactive[Times] -> (StringJoin@Riffle[{##}, " * "]&)];
	Join[
		{TemplateApply[
			"`1` exp(const `1` &x) {\n",
			dualTypeName[n]]},
		{TemplateApply[
			"    const auto t0 = exp(x.``);\n",
			First@dualComponentNames[n]]},
		temporaryVariableDeclarations,
		{"    return {\n"},
		{TemplateApply[
			"        .`` = t0,\n",
			First@dualComponentNames[n]]},
		MapThread[StringTemplate["        .`` = ``,\n"],
			{Rest@dualComponentNames[n], exponentialExpressions}],
		{"    };\n", "}\n"}]];

dualLogDefinition[n_Integer?NonNegative] := Block[
	{logarithmPolynomials, logarithmExpressions,
		temporaryVariableTemplate, temporaryVariableDeclarations},
	logarithmPolynomials = Rest@DualFunctionComponents[
		n, Log, \[FormalX]] /. Thread@Rule[
			Thread@Subscript[\[FormalX], Range[2^n - 1]],
				Subscript[\[FormalX], 0] * Thread@\[FormalT]@Range[2^n - 1]];
	temporaryVariableTemplate = StringTemplate["    const auto `` = `` / " <>
		"x." <> First@dualComponentNames[n] <> ";\n"];
	temporaryVariableDeclarations = MapThread[temporaryVariableTemplate, {
		"t" <> StringJoin[ToString /@ #]& /@ Rest@BinarySubsets[n],
		StringTemplate["x.``"] /@ Rest@dualComponentNames[n]}];
	logarithmExpressions = Table[Block[{
		termPairs = MapAt[StringJoin@Riffle[#, " * "]&,
			MapAt[Switch[Head[#],
					Integer, ToString[#] <> ".0",
					\[FormalT], "t" <> StringJoin[ToString /@
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
		{expr, logarithmPolynomials}];
	Join[
		{TemplateApply[
			"`1` log(const `1` &x) {\n",
			dualTypeName[n]]},
		{TemplateApply[
			"    const auto t0 = log(x.``);\n",
			First@dualComponentNames[n]]},
		temporaryVariableDeclarations,
		{"    return {\n"},
		{TemplateApply[
			"        .`` = t0,\n",
			First@dualComponentNames[n]]},
		MapThread[StringTemplate["        .`` = ``,\n"],
			{Rest@dualComponentNames[n], logarithmExpressions}],
		{"    };\n", "}\n"}]];
