BeginPackage["AlgebraicHypergeometricSeries`"];
algebraicQ::usage="algebraicQ[a,b,c] determines for given parameters a,b,c whether F(a, b; c; x) is algebraic."
algebraicQ2::usage="algebraicQ2[a,b,c] also determines whether F(a, b; c; x) is algebraic but uses for the reducible case a different approach than algebraicQ";
Begin["`Private`"];
Clear[hyperSol]; 
hyperSol[a_, b_, c_] := Module[{\[Alpha], \[Beta], \[Alpha]2, \[Beta]2, l, d, coefs, A, p, i, Sol = {}, L}, 
   \[Alpha] = 1 - c; \[Beta] = c - a - b; A = Tuples[{Which[Element[\[Alpha], Integers], {Min[\[Alpha], 0]}, Element[\[Alpha], Rationals], 
        {\[Alpha], 0}, True, {0}], Which[Element[\[Beta], Integers], {Min[\[Beta], 0]}, Element[\[Beta], Rationals], {0, \[Beta]}, 
        True, {0}]}]; For[i = 1, i <= Length[A], i++, {\[Alpha], \[Beta]} = A[[i]]; 
      d = Floor[-Min[Re[a], Re[b]] - \[Alpha] - \[Beta]]; If[d < 0, Continue[]]; 
      coefs = Table[Module[{pc}, pc], {d + 1}]; p = FromDigits[coefs, x]; 
      l = CoefficientList[((-1 + x)^2*\[Alpha]^2 + a*x*((-1 + x)*(b + \[Alpha]) + x*\[Beta]) + 
           (-1 + x)*\[Alpha]*(1 - c + b*x + 2*x*\[Beta]) + x*\[Beta]*(-c + x*(b + \[Beta])))*p + 
         (-1 + x)*x*(-c - 2*\[Alpha] + x*(1 + a + b + 2*\[Alpha] + 2*\[Beta]))*D[p, x] + (-1 + x)^2*x^2*D[p, {x, 2}], x]; 
      If[l == {}, l = {0}]; L = NullSpace[RowReduce[Table[Coefficient[l[[i]], coefs[[j]]], {i, 1, Length[l]}, 
          {j, 1, d + 1}]]]; Sol = Union[Sol, (Together[x^\[Alpha]*(1 - x)^\[Beta]*FromDigits[#1, x]] & ) /@ L]; ]; 
    Return[Sol]]
Clear[algebraicQ]
algebraicQ[a_, b_, c_] := Module[{Sol, \[Lambda], \[Mu], \[Nu], \[Lambda]P, \[Mu]P, \[Nu]P, \[Lambda]PP, \[Mu]PP, \[Nu]PP, L, 
    SchwarzList = Association[{1/2, 1/3, 1/3} -> "II", {2/3, 1/3, 1/3} -> "III", {1/2, 1/3, 1/4} -> "IV", 
      {2/3, 1/4, 1/4} -> "V", {1/2, 1/3, 1/5} -> "VI", {2/5, 1/3, 1/3} -> "VII", {2/3, 1/5, 1/5} -> "VIII", 
      {1/2, 2/5, 1/5} -> "IX", {3/5, 1/3, 1/5} -> "X", {2/5, 2/5, 2/5} -> "XI", {2/3, 1/3, 1/5} -> "XII", 
      {4/5, 1/5, 1/5} -> "XIII", {1/2, 2/5, 1/3} -> "XIV", {3/5, 2/5, 1/3} -> "XV"]}, 
   If[Element[c, Integers] && NonPositive[c] &&  !((Element[a, Integers] && a > c) || 
        (Element[b, Integers] && b > c)), Throw["Hypergeometric2F1 is not defined"]]; \[Lambda] = 1 - c; \[Mu] = a - b; 
    \[Nu] = c - a - b; If[IntegerQ[a] || IntegerQ[b] || IntegerQ[a - c] || IntegerQ[b - c], 
     If[(Element[a, Integers] && NonPositive[a]) || (Element[b, Integers] && NonPositive[b]), 
       Return["reducible and algebraic"]]; If[((Element[c - a, Integers] && NonPositive[c - a]) || 
         (Element[c - b, Integers] && NonPositive[c - b])) && Element[c - a - b, Rationals], 
       Return["reducible and algebraic"]]; Sol = hyperSol[a, b, c]; If[Length[Sol] > 1, 
       Return["reducible and algebraic"], Return["reducible and transcendental"]]; ]; 
    If[IntegerQ[\[Lambda]] || IntegerQ[\[Mu]] || IntegerQ[\[Nu]], Return["transcendental"]]; 
    If[Count[{\[Lambda], \[Mu], \[Nu]}, _?(RealAbs[Denominator[#1]] == 2 & )] >= 2, 
     Return[StringJoin["algebraic of Schwarz-type ", RomanNumeral[1]]]]; 
    If[Count[{\[Lambda], \[Mu], \[Nu]}, _?(RealAbs[Denominator[#1]] > 5 & )] >= 1, Return["transcendental"]]; 
    {\[Lambda]P, \[Mu]P, \[Nu]P} = RealAbs[Mod[{\[Lambda], \[Mu], \[Nu]}, 2, -1]]; 
    L = MinimalBy[{{\[Lambda]P, \[Mu]P, \[Nu]P}, {\[Lambda]P, 1 - \[Mu]P, 1 - \[Nu]P}, {1 - \[Lambda]P, \[Mu]P, 1 - \[Nu]P}, 
        {1 - \[Lambda]P, 1 - \[Mu]P, \[Nu]P}}, Total][[1]]; {\[Lambda]PP, \[Mu]PP, \[Nu]PP} = Sort[L, Greater]; 
    If[\[Lambda]PP + \[Mu]PP + \[Nu]PP <= 1, Return["transcendental"]]; If[KeyExistsQ[SchwarzList, {\[Lambda]PP, \[Mu]PP, \[Nu]PP}], 
     Return[StringJoin["algebraic of Schwarz-type ", SchwarzList[{\[Lambda]PP, \[Mu]PP, \[Nu]PP}]]], 
     Return["transcendental"]]]
Clear[algebraicQ2]
algebraicQ2[a_, b_, c_] := Module[{\[Lambda], \[Mu], \[Nu], \[Lambda]P, \[Mu]P, \[Nu]P, \[Lambda]PP, \[Mu]PP, \[Nu]PP, L, P, 
    SchwarzList = Association[{1/2, 1/3, 1/3} -> "II", {2/3, 1/3, 1/3} -> "III", {1/2, 1/3, 1/4} -> "IV", 
      {2/3, 1/4, 1/4} -> "V", {1/2, 1/3, 1/5} -> "VI", {2/5, 1/3, 1/3} -> "VII", {2/3, 1/5, 1/5} -> "VIII", 
      {1/2, 2/5, 1/5} -> "IX", {3/5, 1/3, 1/5} -> "X", {2/5, 2/5, 2/5} -> "XI", {2/3, 1/3, 1/5} -> "XII", 
      {4/5, 1/5, 1/5} -> "XIII", {1/2, 2/5, 1/3} -> "XIV", {3/5, 2/5, 1/3} -> "XV"]}, 
   If[Element[c, Integers] && NonPositive[c] &&  !((Element[a, Integers] && a > c && NonPositive[a]) || 
        (Element[b, Integers] && b > c && NonPositive[b])), Throw["Hypergeometric2F1 is not defined"]]; 
    \[Lambda] = 1 - c; \[Mu] = a - b; \[Nu] = c - a - b; If[IntegerQ[a] || IntegerQ[b] || IntegerQ[a - c] || 
      IntegerQ[b - c], If[(Element[a, Integers] && NonPositive[a]) || (Element[b, Integers] && 
         NonPositive[b]), Return["reducible and algebraic"]]; 
      If[((Element[c - a, Integers] && NonPositive[c - a]) || (Element[c - b, Integers] && 
          NonPositive[c - b])) && Element[c - a - b, Rationals], Return["reducible and algebraic"]]; 
      {\[Lambda], \[Mu], \[Nu]} = SortBy[{\[Lambda], \[Mu], \[Nu]}, Boole[ !Element[#1, Integers]] & ]; 
      If[Element[\[Lambda], Integers] && \[Lambda] != 0 && Element[\[Nu], Rationals] &&  !Element[\[Nu], Integers] && 
        Element[\[Mu], Rationals] && ((OddQ[Abs[\[Lambda]] - Abs[\[Mu] + \[Nu]]] && Abs[\[Lambda]] - Abs[\[Mu] + \[Nu]] > 0) || 
         (OddQ[Abs[\[Lambda]] - Abs[\[Mu] - \[Nu]]] && Abs[\[Lambda]] - Abs[\[Mu] - \[Nu]] > 0)), Return["reducible and algebraic"]]; 
      If[Element[\[Lambda], Integers] && Element[\[Mu], Integers] && Element[\[Nu], Integers] && \[Lambda]*\[Mu]*\[Nu] != 0 && 
        OddQ[\[Lambda] + \[Mu] + \[Nu]] && Abs[\[Lambda]] < Abs[\[Mu]] + Abs[\[Nu]] && Abs[\[Mu]] < Abs[\[Lambda]] + Abs[\[Nu]] && 
        Abs[\[Nu]] < Abs[\[Lambda]] + Abs[\[Mu]], Return["reducible and algebraic"], 
       Return["reducible and transcendental"]]]; If[IntegerQ[\[Lambda]] || IntegerQ[\[Mu]] || IntegerQ[\[Nu]], 
     Return["transcendental"]]; If[Count[{\[Lambda], \[Mu], \[Nu]}, _?(RealAbs[Denominator[#1]] == 2 & )] >= 2, 
     Return[StringJoin["algebraic of Schwarz-type ", RomanNumeral[1]]]]; 
    If[Count[{\[Lambda], \[Mu], \[Nu]}, _?(RealAbs[Denominator[#1]] > 5 & )] >= 1, Return["transcendental"]]; 
    {\[Lambda]P, \[Mu]P, \[Nu]P} = RealAbs[Mod[{\[Lambda], \[Mu], \[Nu]}, 2, -1]]; 
    L = MinimalBy[{{\[Lambda]P, \[Mu]P, \[Nu]P}, {\[Lambda]P, 1 - \[Mu]P, 1 - \[Nu]P}, {1 - \[Lambda]P, \[Mu]P, 1 - \[Nu]P}, 
        {1 - \[Lambda]P, 1 - \[Mu]P, \[Nu]P}}, Total][[1]]; {\[Lambda]PP, \[Mu]PP, \[Nu]PP} = Sort[L, Greater]; 
    If[\[Lambda]PP + \[Mu]PP + \[Nu]PP <= 1, Return["transcendental"]]; If[KeyExistsQ[SchwarzList, {\[Lambda]PP, \[Mu]PP, \[Nu]PP}], 
     Return[StringJoin["algebraic of Schwarz-type ", SchwarzList[{\[Lambda]PP, \[Mu]PP, \[Nu]PP}]]], 
     Return["transcendental"]]]
End[];
EndPackage[];
