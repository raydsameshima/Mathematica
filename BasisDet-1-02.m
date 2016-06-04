(*BasisDet ver 1.02*)(*Define the polynomial ordering*)
PolyOrder = DegreeLexicographic;


(*Setup:from the propogators to cut equations in scalar products*)

PreTreatment[] := 
 Module[{AdditionalKinematics1, AdditionalKinematics2, 
   KinematicsCondition, LoopMomentaList, ExternalMomentaList, 
   RemindingMomentaList, MomentaProjection, ScalarProduct, i, j, 
   len},(*n=Length[ExternalMomentaBasis]+1;*)
  LoopMomentaList = Table[ToExpression["l" <> ToString[i]], {i, 1, L}];
  ExternalMomentaList = 
   Table[ToExpression["p" <> ToString[i]], {i, 1, n}];
  RemindingMomentaList = 
   Complement[ExternalMomentaList, ExternalMomentaBasis];
  physicalDimension = Dim /. \[Epsilon] -> 0;
  If[Coefficient[Dim, \[Epsilon]] == 0, ExtraDimensionFlag = 0, 
   ExtraDimensionFlag = 1];
  xtable = 
   Table[ToExpression["x" <> ToString[i] <> ToString[j]], {i, 1, 
     L}, {j, 1, physicalDimension}];
  mutable = {};
  If[ExtraDimensionFlag == 1, 
   mutable = 
    Table[ToExpression["\[Mu]" <> ToString[i] <> ToString[j]], {i, 1, 
      L}, {j, 1, L}];
   For[i = 1, i <= L, i++, 
    For[j = 1, j < i, j++, mutable[[i, j]] = mutable[[j, i]];];];];
  NSpurious = physicalDimension - n + 1;
  If[NSpurious < 0, NSpurious = 0];
  SpuriousMomentaList = 
   Table[ToExpression["\[Omega]" <> ToString[i]], {i, 1, NSpurious}];
  SpacetimeBasis = Join[ExternalMomentaBasis, SpuriousMomentaList];
  TotalMomentaList = 
   Join[LoopMomentaList, SpacetimeBasis, RemindingMomentaList];
  Print["Physical spacetime basis is ", SpacetimeBasis];
  AdditionalKinematics1 = 
   Table[ExternalMomentaList[[i]]*SpuriousMomentaList[[j]] -> 0, {i, 
      1, Length[ExternalMomentaList]}, {j, 1, 
      Length[SpuriousMomentaList]}] // Flatten;
  AdditionalKinematics2 = 
   Table[SpuriousMomentaList[[i]]*SpuriousMomentaList[[j]] -> 0, {i, 
      1, Length[SpuriousMomentaList]}, {j, i + 1, 
      Length[SpuriousMomentaList]}] // Flatten;
  (*This is the scalar product list for all vectors in the spacetime \
basis*)KinematicsCondition = 
   Join[Kinematics, AdditionalKinematics1, AdditionalKinematics2];
  Gram = Table[
    SpacetimeBasis[[i]]*SpacetimeBasis[[j]], {i, 1, 
     Length[SpacetimeBasis]}, {j, 1, Length[SpacetimeBasis]}];
  ExtendGram = 
   Table[RemindingMomentaList[[i]]*SpacetimeBasis[[j]], {i, 1, 
     Length[RemindingMomentaList]}, {j, 1, Length[SpacetimeBasis]}];
  Gram = Gram //. KinematicsCondition;
  ExtendGram = ExtendGram //. KinematicsCondition;
  (*Print[RemindingMomentaList];*)
  If[Length[RemindingMomentaList] == 1, 
   ExtendGram = {-Sum[
        Gram[[j]], {j, 1, physicalDimension - NSpurious}] // 
      Simplify}];
  (*This is the list for scalar products of loop momenta,
  All external momenta,
  spurious momenta vs vectors in the spacetime basis*)
  MomentaProjection = Join[xtable, Gram, ExtendGram];
  ScalarProduct = 
   Table[MomentaProjection[[i]].Inverse[Gram].MomentaProjection[[j]] //
      Simplify, {i, 1, Length[TotalMomentaList]}, {j, 1, 
     Length[TotalMomentaList]}];
  If[ExtraDimensionFlag == 
    1, {Print["Extra dimension is turned on."];
    For[i = 1, i <= L, i++, 
     For[j = 1, j <= L, j++, 
       ScalarProduct[[i, j]] -= mutable[[i, j]];];];}];
  ScalarProductRules = 
   Table[TotalMomentaList[[i]]*TotalMomentaList[[j]] -> 
     ScalarProduct[[i, j]], {i, 1, Length[TotalMomentaList]}, {j, i, 
     Length[TotalMomentaList]}];
  ScalarProductRules = Flatten[ScalarProductRules];
  SPList = 
   Join[Flatten[Reverse[Transpose[xtable]]], 
    Union[Flatten[mutable]]];
  len = Length[RenormalizationCondition];
  RenormalizationLoopMomenta = 
   Table[RenormalizationCondition[[i, 1]], {i, 1, len}];
  RenormalizationPower = 
   Table[RenormalizationCondition[[i, 2]], {i, 1, len}];]



(*This function removes the overall coefficient from one polynomial.*)

RemoveCoefficient[poly0_, VarList0_] := 
 Module[{exp, list, len, ParaList, poly = poly0, VarList = VarList0, 
   Replace, list1, i, result = 1, Vlist}, 
  exp = Numerator[Together[poly]];
  If[exp == 0, Return[0];];
  ParaList = Complement[Variables[exp], VarList];
  Replace = Table[ParaList[[i]] -> 0, {i, 1, Length[ParaList]}];
  list = FactorTermsList[exp, VarList];
  len = Length[list];
  For[i = 1, i <= len, i++, 
   Vlist = Complement[Variables[list[[i]]], ParaList];
   If[Vlist == {}, Continue[]];
   result *= list[[i]];];
  Return[result];]


(*This function convert a monomial to a list of its powers in \
variables*)

ExpRead[monomial_, VarList_] := Exponent[monomial, VarList];
(*This function convert a list of powers in variables to a monomial*)
\

ExpRecover[list_, VarList_] := Inner[Power, VarList, list, Times];




(*Generate the set of cut equations in ALL scalar \
products.op=0,numeric.op=1,analytic*)

CutGenerator[op_] := 
 Module[{option = op, num}, If[option == 0, num = numeric, num = {}];
  CutEqn = 
   Table[Expand[Props[[i]]^2] //. ScalarProductRules // Simplify, {i, 
     1, Length[Props]}];
  CutEqn = 
   Table[RemoveCoefficient[CutEqn[[i]] //. num, SPList] // 
     Simplify, {i, 1, Length[CutEqn]}];]

(*This function identify all the variables which can expressed as \
linear functions of the other variables plus polynomials in the \
ideal.It has various usage.Here it is used for ISP identification.*)

LinearReduce[ideal1_, Varlist1_] := 
 Module[{ideal = ideal1, Varlist = Varlist1, PreGr, PreLTList, expr, 
   ISPlist, RSP, ISP, reducedIdeal, RSPSolution, templist, i, j}, 
  PreGr = GroebnerBasis[ideal, Varlist, MonomialOrder -> PolyOrder, 
    CoefficientDomain -> RationalFunctions];
  PreLTList = 
   Table[MonomialList[PreGr[[i]], Varlist, PolyOrder][[1]], {i, 1, 
     Length[PreGr]}];
  RSP = {};
  For[i = 1, i <= Length[PreLTList], i++, expr = PreLTList[[i]];
   j = Total[Exponent[expr, Varlist]];
   If[j == 1, 
    RSP = Append[RSP, ExpRecover[Exponent[expr, Varlist], Varlist]]];];
  RSPSolution = 
   Table[RSP[[i]] -> 
      PolynomialReduce[RSP[[i]], PreGr, Varlist, 
        MonomialOrder -> PolyOrder][[2]] // Simplify, {i, 1, 
     Length[RSP]}];
  reducedIdeal = Union[ideal //. RSPSolution // Simplify];
  (*Sort the ISP*)
  ISP = MonomialList[Total[Complement[Varlist, RSP]], Varlist, 
    PolyOrder];
  If[ISP == {0}, ISP = {}];
  reducedIdeal = 
   Table[RemoveCoefficient[reducedIdeal[[i]], ISP] // Simplify, {i, 1,
      Length[reducedIdeal]}];
  reducedIdeal = Union[reducedIdeal];
  templist = {};
  For[i = 1, i <= Length[reducedIdeal], i++, 
   If[reducedIdeal[[i]] == 0, Continue[]];
   templist = Append[templist, reducedIdeal[[i]]];];
  Return[{ISP, RSPSolution, templist}];]
VariableInterpretation[xx0_] := 
 Module[{xx = xx0, i, j, s, t}, 
  For[i = 1, i <= L, i++, 
   For[j = 1, j <= physicalDimension, j++, 
     If[xtable[[i, j]] == xx, s = i; t = j; Return[{1, s, t}]];];];
  For[i = 1, i <= L, i++, 
   For[j = i, j <= L, j++, 
     If[mutable[[i, j]] == xx, s = i; t = j; Return[{2, s, t}]];];];
  Return[-1];]

(*Generate the ISP's.Determine its dependence in the loop momenta*)

ISPTreatment[] := 
 Module[{i, j, len, sign, k, l, komega, 
   tempPowerList}, {ISP, RSPSolution, CutEqnISP} = 
   LinearReduce[CutEqn, SPList];
  len = Length[ISP];
  ISPLoopMomentaTable = Table[0, {i, 1, len}, {j, 1, L}];
  ISPSpuriousMomentaTable = Table[0, {i, 1, len}, {j, 1, NSpurious}];
  (*Find the maximal power of each loop momenta*)
  LoopMomentaPowerList = tempPowerList = Table[0, {i, 1, L}];
  For[i = 1, i <= L, i++, tempPowerList = Table[0, {i, 1, L}];
   tempPowerList[[i]] = 1;
   For[j = 1, j <= Length[RenormalizationLoopMomenta], j++, 
    If[RenormalizationLoopMomenta[[j]] == tempPowerList, 
      LoopMomentaPowerList[[i]] = RenormalizationPower[[j]];
      Break[];];];];
  For[i = 1, i <= len, 
   i++, {sign, k, l} = VariableInterpretation[ISP[[i]]];
   If[sign == 1, ISPLoopMomentaTable[[i, k]]++;];
   If[sign == 2, ISPLoopMomentaTable[[i, k]]++;
    ISPLoopMomentaTable[[i, l]]++;];
   komega = l - physicalDimension + NSpurious;
   If[komega > 0 && sign == 1, 
    ISPSpuriousMomentaTable[[i, komega]]++];];
  ISPPowerList = {};
  If[len > 0, 
   ISPPowerList = ISPLoopMomentaTable.LoopMomentaPowerList];]


TestFunction[x_] := Piecewise[{{1, x >= 0}, {I, x < 0}}];
Compare[list10_, list20_] := 
 Module[{list1 = list10, list2 = list20, list, len, flag}, 
  If[list1 == list2, Return[0]];
  list = list1 - list2;
  flag = Sum[TestFunction[list[[i]]], {i, 1, Length[list]}];
  If[Im[flag] > 0, Return[-1], Return[1]];]


RenorTest[list0_] := 
 Module[{list = list0, list2, flag, exp, i, n}, 
  list2 = list.ISPLoopMomentaTable;
  For[i = 1, i <= Length[RenormalizationLoopMomenta], i++, 
   n = RenormalizationLoopMomenta[[i]].list2;
   If[n > RenormalizationPower[[i]], Return[0]];];
  Return[1];]
SpuriousTest[list0_] := 
 Module[{list = list0, list2, SpuriousCounting, i, exp, sign = 0}, 
  list2 = list.ISPSpuriousMomentaTable;
  For[i = 1, i <= NSpurious, i++, 
   If[Mod[list2[[i]], 2] == 1, sign = 1; Break[];];];
  Return[sign];]
Tick[list1_, PowerList1_] := 
 Module[{list = list1, PowerList = PowerList1, result, i, len}, 
  len = Length[list];
  result = list;
  For[i = len, i >= 1, i--, result[[i]]++;
   If[result[[i]] <= PowerList[[i]], Break[];];
   result[[i]] = 0;];
  Return[result];]

LoopMomentum[n_] := Module[{result},
  result = Inverse[Gram].xtable[[n]] /. RSPSolution // Simplify;
  Return[result];
  ]


GenerateBasis[op_] := 
 Module[{option = op, ttt, TempMonoList, TempExpList, TargetCount = 0,
    TargetPower, SpuriousCount, NonRenorCount, r, ThisTerm, i, j, 
   k = 0, ISPPowerUpLimit, len, StopSign}, ttt = TimeUsed[];
  ISPPowerUpLimit = 4;
  PreTreatment[];
  CutGenerator[option];
  ISPTreatment[];
  len = Length[ISP];
  Print["Number of irreducible scalar products: ", len];
  Print["Irreducible Scalar Products:", ISP];
  Print["Cut equations for ISP are listed in the variable \
'CutEqnISP'"];
  Basis = {};
  SpuriousBasis = {};
  NSpuriousBasis = {};
  TempMonoList = {};
  TempExpList = {};
  SpuriousCount = 0;
  NonRenorCount = 0;
  Gr = GroebnerBasis[CutEqnISP, ISP, MonomialOrder -> PolyOrder, 
    CoefficientDomain -> RationalFunctions];
  (*LTList=Table[MonomialList[Gr[[i]],ISP,PolyOrder][[1]],{i,1,Length[
  Gr]}];*)TargetPower = Table[0, {i, 1, len}];
  StopSign = 0;
  If[Gr == {1}, StopSign = 1];
  While[StopSign == 0,(*TargetPower=IntegerDigits[
   i,(ISPPowerUpLimit+1),len];*)(*If[i==Floor[(ISPPowerUpLimit+1)^len*
   k/100],Print[k/100*100,"%     ",TimeUsed[]-ttt];k++];*)
   If[RenorTest[TargetPower] == 1, TargetCount++;
    r = PolynomialReduce[ExpRecover[TargetPower, ISP], Gr, ISP, 
       MonomialOrder -> PolyOrder][[2]];
    TempMonoList = MonomialList[r, ISP, PolyOrder];
    TempExpList = 
     Table[ExpRead[TempMonoList[[j]], ISP], {j, 1, 
       Length[TempMonoList]}];
    If[r == 0, TempExpList = {}];
    Basis = Union[Basis, TempExpList];];
   TargetPower = Tick[TargetPower, ISPPowerList];
   If[TargetPower == Table[0, {i, 1, len}], StopSign = 1];];
  Integrand = 0;
  For[j = 1, j <= Length[Basis], j++, ThisTerm = cc[];
   For[i = 1, i <= Length[ISP], i++, 
    ThisTerm = ThisTerm*c[i, Basis[[j, i]]]*ISP[[i]]^Basis[[j, i]];];
   For[i = 1, i <= Length[ISP], i++, 
    ThisTerm = ThisTerm //. cc[x1___]*c[i, x2_] -> cc[x1, x2]];
   Integrand = Integrand + ThisTerm;];
  Print["Possible renormalizable terms: ", TargetCount];
  For[i = 1, i <= Length[Basis], i++, 
   If[SpuriousTest[Basis[[i]]] == 1, SpuriousCount++;
     SpuriousBasis = Append[SpuriousBasis, Basis[[i]]];];];
  NSpuriousBasis = Complement[Basis, SpuriousBasis];
  For[i = 1, i <= Length[Basis], i++, 
   If[RenorTest[Basis[[i]]] == 0, NonRenorCount++];];
  Print[];
  Print["The basis contains ", Length[Basis], 
   " terms, which are listed in the variable 'Basis'"];
  Print["The explicit form of the integrand is listed in the variable \
'Integrand'"];
  Print["Number of spurious terms: ", SpuriousCount, 
   ", listed in the variable 'SpuriousBasis'"];
  Print["Number of non-spurious terms: ", 
   Length[Basis] - SpuriousCount, 
   ", listed in the variable 'NSpuriousBasis'"];
  (*Print["Number of non-renormalizable terms: ",NonRenorCount];*)
  Print["Time used: ", TimeUsed[] - ttt, " seconds"];]