(* ::Package:: *)

Needs["CCodeGenerator`"];

CChainedIf[{cond_}, {expr_}, default_] :=
	CIf[cond, expr, default];
CChainedIf[{cond_, conds__}, {expr_, exprs__}, default_] :=
	CIf[cond, expr, CChainedIf[{conds}, {exprs}, default]];

lowerFirst[""] = "";
lowerFirst[s_String] := ToLowerCase[StringTake[s, 1]] <>
	StringDrop[s, 1];


func = HermiteHi;
funcName = lowerFirst@ToString[func];
nMax = 255;

cpolys = Table[HornerForm[func[n, "x"], "x"], {n, 0, nMax}] //.
	{"x"^2 -> "x2", n_Integer :> ToString[n] <> ".0"} //.
	Plus[Times[a_, b_], c_] :> CCall["std::fma", {a, b, c}] //.
	Plus[arg_, args__] :> COperator[Plus, {arg, args}] //.
	Times[arg_, args__] :> COperator[Times, {arg, args}];

cconds = Table[COperator[Equal, {"n", n}], {n, 0, nMax}];

cexcept = CStatement[
	"throw std::invalid_argument(\"argument n of " <>
		funcName <> "(n, x) out of range\")"];

ccode = ToCCodeString@CFunction["double", funcName,
	{{"int", "n"}, {"double", "x"}}, {
		CDeclare["double", "x2 = x * x"],
		CChainedIf[cconds, CReturn /@ cpolys, cexcept]}];

ccode = FixedPoint[StringReplace[{
	")\n{" -> ") {",
	"}\nelse" -> "} else",
	"if( " -> "if (",
	"else\n{" -> "else {"
}], ccode];

Export[funcName <> ".inc", ccode, "Text"];
