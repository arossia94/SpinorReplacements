(* ::Package:: *)

BeginPackage["LCeps4eval`"]


LCeps4evalRule::usage = "To do"


Begin["`Private`"]


(* Evaluation rule for the parity-odd Levi-Civita objects appearing in
   amp_SpinProd_4pt_WWWW_h1h2h3h4_photon_general.dat .
   LCeps4[A,B,C,D] = eps^{mu nu rho sig} A_mu B_nu C_rho D_sig   (eps^{0123}=+1, metric diag(1,-1,-1,-1)),
   where the args are tags:  eps[i] = hi-polarization vector of leg i,   pmom[i] = momentum p_i.
   R-pol vector eps[i] = tr\[Gamma]Sq["i"[1],"i"[1]]/(Sqrt[2] MW)  (the package's massive epsPlus[i]).
   Apply AFTER reempSpinProd (for the eps[i]) and momReplacement (for pmom[i]). *)
LCeps4evalRule[momreplacement_, polsettings_, polVecEval_] := Module[{gmet, LCt, e, pm},
  gmet = DiagonalMatrix[{1, -1, -1, -1}];
  LCt = Normal[LeviCivitaTensor[4]];
  e[i_] := (Piecewise[{{\[Epsilon]Plus,StringTake[polsettings,{i}]=="+"},{\[Epsilon]Minus,StringTake[polsettings,{i}]=="-"},
{\[Epsilon]0,StringTake[polsettings,{i}]=="0"}}][i]/.polVecEval);
  pm[i_] := Table[ToExpression["p" <> ToString[i]][mu], {mu, 4}]/.momreplacement;
  {LCeps4[A_, B_, C_, D_] :> Module[{v},
      v = {A, B, C, D}/.{eps[i_] :> e[i], pmom[i_] :> pm[i]};
      Sum[LCt[[m, n, r, s]] v[[1, m]] v[[2, n]] v[[3, r]] v[[4, s]] gmet[[m, m]] gmet[[n, n]] gmet[[r, r]] gmet[[s, s]], {m, 4}, {n, 4}, {r, 4}, {s, 4}]]}
]
(* usage:
     polsettings=polstr (*h1h2h3h4 in +/-/0 notation.*)
     amp = Get["amp_SpinProd_4pt_WWWW_h1h2h3h4_photon_general.dat"];
     sp  = reempSpinProd[kin, rnd];  mom = momReplacement[kin];
     rndSpinorSet=randomSpinors[];
     polVecs=polVectors[kin,sp,rndSpinorSet];
     val = amp /. {gWWA-related coupling substitutions, \[CapitalLambda]->..., MW->...}
               /. LCeps4evalRule[mom,polsettings,Flatten[polVecs]] /. sp /. mom ;
   (brackets trBrKt/sqBrKt come from sp; momentum components p_i[mu] from mom).            *)


End[];
EndPackage[];
