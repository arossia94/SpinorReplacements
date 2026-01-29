(* ::Package:: *)

(* ::Package:: *)
(* SpinorReplacements Package *)
(* Combines mosca KinematicSubstitution with custom spinor replacement functions *)


BeginPackage["SpinorReplacements`"];

(* Load the external packages needed *)
$ContextPath = Join[{"SpinorReplacements`","ExternalPackages`KinematicSubstitution`"}, $ContextPath];

(* Public function declarations for custom spinor functions *)
generateKinematics::usage = "generateKinematics[nF,nV,nS,{m1,...,mN}] generates a kinematics phase space point. It is the 
moniker for a modified version of the original KinematicConfigurations of the mosca package."
reempSpinProd::usage = "reempSpinProd[genKin] generates spinor product replacement rules from kinematic configurations.";
randomSpinors::usage = "randomSpinors[] generates random reference spinors for polarization vectors.";
polVectors::usage = "polVectors[kinConfigs, reempSpinors] computes polarization vectors.";
momReplacement::usage = "momReplacement[kinConfigs] generates momentum replacement rules.";
replacePolVecs::usage = "replacePolVecs[pol, polVecEval] generates polarization vector replacement rules.";
eqToMatch::usage = "eqToMatch[ampOS, ampSMEFT, pol] computes the difference between on-shell and SMEFT amplitudes.";

(* Spinor bracket notation *)
sqBrKt::usage = "Square spinor bracket [i|j\:27e9.";
trBrKt::usage = "Triangular spinor bracket \:27e8i|j].";
sq\[Gamma]Tr::usage = "\:27e8i|\[Gamma]^\[Mu]|j].";
tr\[Gamma]Sq::usage = "\:27e8i|\[Gamma]^\[Mu]|j\:27e9.";
sqPPsq::usage = "\:27e8i|p q|j\:27e9.";
trPPtr::usage = "\:27e8i|p q|j].";
sqPtr::usage = "[i|p|j].";
trPsq::usage = "\:27e8i|p|j\:27e9.";

(* Polarization symbols *)
\[Epsilon]Plus::usage = "Positive helicity polarization vector.";
\[Epsilon]Minus::usage = "Negative helicity polarization vector.";
\[Epsilon]0::usage = "Longitudinal polarization vector.";

(* Mass symbols for massive particles *)
masP::usage = "Mass parameter for massive particle.";

Begin["`Private`"];

(* ========================================================================= *)
(* PART 1: KinematicSubstitution from mosca (modified version)              *)
(* ========================================================================= *)

(* Load mosca's NumericalKinematics *)
(*Get["SpinorReplacements`ExternalPackages`NumericalKinematics`"];*)
Get["SpinorReplacements`ExternalPackages`KinematicSubstitution`"];
generateKinematics[nF_,nV_,nS_,masses_:0]:=KinematicConfigurations[nF,nV,nS,masses];


(* ========================================================================= *)
(* PART 2: Custom Spinor Replacement Functions                              *)
(* ========================================================================= *)
reempSpinProd[genKin_]:=Module[{listUs,listVBs,listPs,pR,pL,listAllParts,listMasses,listMassless,listMassive,ret,strMasP,minkoMetric},
minkoMetric=DiagonalMatrix[{1,-1,-1,-1}];
listUs=genKin["u"];
listVBs=genKin["vbar"];
listPs=genKin["p"];
listAllParts=Table[kk,{kk,1,Length[listPs]}];
listMasses=Table[FullSimplify[MDot[listPs[[j]],listPs[[j]]]],{j,listAllParts}];
(*/// We're using a modified mosca that makes the definition of gamma5 and all the gammas public. ///*)
(*gamma5=DiagonalMatrix[{-1,-1,1,1}];*)
pR=(IdentityMatrix[4]+gamma5)/2;
pL=(IdentityMatrix[4]-gamma5)/2;
listMassless=Position[listMasses,0]//Flatten;
listMassive=Complement[listAllParts,listMassless];
strMasP[j_]:=Piecewise[{{masP[ToString[j]],MemberQ[listMassive,j]}},ToString[j]];
(*/// Compute massless product spinors for massless momenta. ///*);
ret=Join[DeleteCases[Flatten[Table[If[i1!=i2,sqBrKt[ToString[i1],ToString[i2]]->listVBs[[i1]] . pR . listUs[[i2]],"0"],{i1,listMassless},{i2,listMassless}]],a_/;a==="0"],
DeleteCases[Flatten[Table[If[i1!=i2,trBrKt[ToString[i1],ToString[i2]]->listVBs[[i1]] . pL . listUs[[i2]],"0"],{i1,listMassless},{i2,listMassless}]],a_/;a==="0"]
];
(*/// Compute [p|q], <p|q>, [q|p], <q|p> with p massless and q massive.///*)
ret=Join[ret,
Flatten[Table[{trBrKt[ToString[i1],ToString[i2][subi2]]->listVBs[[i1]] . pL . listUs[[i2]][[subi2]],trBrKt[ToString[i2][subi2],ToString[i1]]->
listVBs[[i2]][[subi2]] . pL . listUs[[i1]]
},{i1,listMassless},{i2,listMassive},{subi2,1,2}]],
Flatten[Table[{sqBrKt[ToString[i1],ToString[i2][subi2]]->listVBs[[i1]] . pR . listUs[[i2]][[subi2]],sqBrKt[ToString[i2][subi2],ToString[i1]]->
listVBs[[i2]][[subi2]] . pR . listUs[[i1]]
},{i1,listMassless},{i2,listMassive},{subi2,1,2}]]
];
(*/// Compute [p|q], <p|q>, [q|p], <q|p> with p and q massive.///*)
ret=Join[ret,
Flatten[Table[trBrKt[ToString[i1][subi1],ToString[i2][subi2]]->Simplify[listVBs[[i1]][[subi1]] . pL . listUs[[i2]][[subi2]]],{i1,listMassive},{i2,listMassive},{subi1,1,2},{subi2,1,2}]],
Flatten[Table[sqBrKt[ToString[i1][subi1],ToString[i2][subi2]]->Simplify[listVBs[[i1]][[subi1]] . pR . listUs[[i2]][[subi2]]],{i1,listMassive},{i2,listMassive},{subi1,1,2},{subi2,1,2}]]
];
(*/// Compute <p|\[Gamma]^\[Mu]|q] and <q|\[Gamma]^\[Mu]|p] for massless momenta. ///*);
ret=Join[ret,
DeleteCases[Flatten[Table[If[i1!=i2,sq\[Gamma]Tr[ToString[i1],ToString[i2]]->Table[listVBs[[i1]] . pR . gammas[[jj]] . pL . listUs[[i2]],{jj,1,4}],"0"],{i1,listMassless},{i2,listMassless}]],a_/;a==="0"],
DeleteCases[Flatten[Table[If[i1!=i2,tr\[Gamma]Sq[ToString[i1],ToString[i2]]->Table[listVBs[[i1]] . pL . gammas[[jj]] . pR . listUs[[i2]],{jj,1,4}],"0"],{i1,listMassless},{i2,listMassless}]],a_/;a==="0"]
];
(*/// Compute <p|\[Gamma]^\[Mu]|q] and <q|\[Gamma]^\[Mu]|p] for q massive and p massless. ///*)
ret=Join[ret,
Flatten[Table[sq\[Gamma]Tr[ToString[i1],ToString[i2][subi2]]->Table[listVBs[[i1]] . pR . gammas[[jj]] . pL . listUs[[i2]][[subi2]],{jj,1,4}],{i1,listMassless},{i2,listMassive},{subi2,1,2}]],
Flatten[Table[tr\[Gamma]Sq[ToString[i1],ToString[i2][subi2]]->Table[listVBs[[i1]] . pL . gammas[[jj]] . pR . listUs[[i2]][[subi2]],{jj,1,4}],{i1,listMassless},{i2,listMassive},{subi2,1,2}]],
Flatten[Table[tr\[Gamma]Sq[ToString[i1][subi1],ToString[i2]]->Table[listVBs[[i1]][[subi1]] . pL . gammas[[jj]] . pR . listUs[[i2]],{jj,1,4}],{i1,listMassive},{i2,listMassless},{subi1,1,2}]],
Flatten[Table[sq\[Gamma]Tr[ToString[i1][subi1],ToString[i2]]->Table[listVBs[[i1]][[subi1]] . pR . gammas[[jj]] . pL . listUs[[i2]],{jj,1,4}],{i1,listMassive},{i2,listMassless},{subi1,1,2}]]
];
(*/// Compute <p|\[Gamma]^\[Mu]|q] and <q|\[Gamma]^\[Mu]|p] for q and p massive. ///*)
ret=Join[ret,
Flatten[Table[sq\[Gamma]Tr[ToString[i1][subi1],ToString[i2][subi2]]->Table[listVBs[[i1]][[subi1]] . pR . gammas[[jj]] . pL . listUs[[i2]][[subi2]],{jj,1,4}],{i1,listMassive},{i2,listMassive},{subi1,1,2},{subi2,1,2}]],
Flatten[Table[tr\[Gamma]Sq[ToString[i1][subi1],ToString[i2][subi2]]->Table[listVBs[[i1]][[subi1]] . pL . gammas[[jj]] . pR . listUs[[i2]][[subi2]],{jj,1,4}],{i1,listMassive},{i2,listMassive},{subi1,1,2},{subi2,1,2}]]
];
(*/// Compute <p|K|q] and <q|K|p] for massless p,q and general on-shell K. ///*)
ret=Join[ret,
Flatten[Table[
trPsq[ToString[i1],strMasP[i3],ToString[i2]]->Simplify[MDot[listPs[[i3]],
Table[listVBs[[i1]] . pL . gammas[[jj]] . pR . listUs[[i2]],{jj,1,4}]]]
,{i1,listMassless},{i2,listMassless},{i3,listAllParts}]
],
Flatten[Table[
sqPtr[ToString[i1],strMasP[i3],ToString[i2]]->Simplify[MDot[listPs[[i3]],
Table[listVBs[[i1]] . pR . gammas[[jj]] . pL . listUs[[i2]],{jj,1,4}]]]
,{i1,listMassless},{i2,listMassless},{i3,listAllParts}]]
];
(*/// Compute <p|K|q] and <q|K|p] for massless p, massive q and general on-shell K. ///*)
ret=Join[ret,
Flatten[Table[
{trPsq[ToString[i1],strMasP[i3],ToString[i2][subi2]]->Simplify[MDot[listPs[[i3]],
Table[listVBs[[i1]] . pL . gammas[[jj]] . pR . listUs[[i2]][[subi2]],{jj,1,4}]]],
trPsq[ToString[i2][subi2],strMasP[i3],ToString[i1]]->Simplify[MDot[listPs[[i3]],
Table[listVBs[[i2]][[subi2]] . pL . gammas[[jj]] . pR . listUs[[i1]],{jj,1,4}]]]
},{i1,listMassless},{i2,listMassive},{subi2,1,2},{i3,listAllParts}]
],
Flatten[Table[
{sqPtr[ToString[i1],strMasP[i3],ToString[i2][subi2]]->Simplify[MDot[listPs[[i3]],
Table[listVBs[[i1]] . pR . gammas[[jj]] . pL . listUs[[i2]][[subi2]],{jj,1,4}]]],
sqPtr[ToString[i2][subi2],strMasP[i3],ToString[i1]]->Simplify[MDot[listPs[[i3]],
Table[listVBs[[i2]][[subi2]] . pR . gammas[[jj]] . pL . listUs[[i1]],{jj,1,4}]]]
},{i1,listMassless},{i2,listMassive},{subi2,1,2},{i3,listAllParts}]
]
];
(*/// Compute <p|K|q] and <q|K|p] for massive p and q and general on-shell K. ///*)
ret=Join[ret,
Flatten[Table[
trPsq[ToString[i1][subi1],strMasP[i3],ToString[i2][subi2]]->Simplify[MDot[listPs[[i3]],
Table[listVBs[[i1]][[subi1]] . pL . gammas[[jj]] . pR . listUs[[i2]][[subi2]],{jj,1,4}]]]
,{i1,listMassive},{i2,listMassive},{subi1,1,2},{subi2,1,2},{i3,listAllParts}]],
Flatten[Table[
sqPtr[ToString[i1][subi1],strMasP[i3],ToString[i2][subi2]]->Simplify[MDot[listPs[[i3]],
Table[listVBs[[i1]][[subi1]] . pR . gammas[[jj]] . pL . listUs[[i2]][[subi2]],{jj,1,4}]]],{i1,listMassive},{i2,listMassive},{subi1,1,2},{subi2,1,2},{i3,listAllParts}]
]
];
(*/// Compute [p|K L |q] and <p| K L | q> for massless p,q and on-shell K, L. ///*)
ret=Join[ret,
Flatten[Table[
sqPPsq[ToString[i1],strMasP[i3],strMasP[i4],ToString[i2]]->Simplify[Sum[minkoMetric[[\[Mu],\[Mu]]]*minkoMetric[[\[Nu],\[Nu]]]*listPs[[i3]][[\[Mu]]]*listPs[[i4]][[\[Nu]]]*
listVBs[[i1]] . pR . gammas[[\[Mu]]] . gammas[[\[Nu]]] . pR . listUs[[i2]],{\[Mu],1,4},{\[Nu],1,4}]]
,{i1,listMassless},{i2,listMassless},{i3,listAllParts},{i4,listAllParts}]],
Flatten[Table[
trPPtr[ToString[i1],strMasP[i3],strMasP[i4],ToString[i2]]->Simplify[Sum[minkoMetric[[\[Mu],\[Mu]]]*minkoMetric[[\[Nu],\[Nu]]]*listPs[[i3]][[\[Mu]]]*listPs[[i4]][[\[Nu]]]*
listVBs[[i1]] . pL . gammas[[\[Mu]]] . gammas[[\[Nu]]] . pL . listUs[[i2]],{\[Mu],1,4},{\[Nu],1,4}]]
,{i1,listMassless},{i2,listMassless},{i3,listAllParts},{i4,listAllParts}]]
];
(*/// Compute [p|K L |q] and <p| K L | q> for massless p, massive q and on-shell K, L. ///*)
ret=Join[ret,
Flatten[Table[{
sqPPsq[ToString[i1],strMasP[i3],strMasP[i4],ToString[i2][subi2]]->Simplify[Sum[minkoMetric[[\[Mu],\[Mu]]]*minkoMetric[[\[Nu],\[Nu]]]*listPs[[i3]][[\[Mu]]]*listPs[[i4]][[\[Nu]]]*
listVBs[[i1]] . pR . gammas[[\[Mu]]] . gammas[[\[Nu]]] . pR . listUs[[i2]][[subi2]],{\[Mu],1,4},{\[Nu],1,4}]],
sqPPsq[ToString[i2][subi2],strMasP[i3],strMasP[i4],ToString[i1]]->Simplify[Sum[minkoMetric[[\[Mu],\[Mu]]]*minkoMetric[[\[Nu],\[Nu]]]*listPs[[i3]][[\[Mu]]]*listPs[[i4]][[\[Nu]]]*
listVBs[[i2]][[subi2]] . pR . gammas[[\[Mu]]] . gammas[[\[Nu]]] . pR . listUs[[i1]],{\[Mu],1,4},{\[Nu],1,4}]]
}
,{i1,listMassless},{i2,listMassive},{subi2,1,2},{i3,listAllParts},{i4,listAllParts}]
],
Flatten[Table[
{trPPtr[ToString[i1],strMasP[i3],strMasP[i4],ToString[i2][subi2]]->Simplify[Sum[minkoMetric[[\[Mu],\[Mu]]]*minkoMetric[[\[Nu],\[Nu]]]*listPs[[i3]][[\[Mu]]]*listPs[[i4]][[\[Nu]]]*
listVBs[[i1]] . pL . gammas[[\[Mu]]] . gammas[[\[Nu]]] . pL . listUs[[i2]][[subi2]],{\[Mu],1,4},{\[Nu],1,4}]],
trPPtr[ToString[i2][subi2],strMasP[i3],strMasP[i4],ToString[i1]]->Simplify[Sum[minkoMetric[[\[Mu],\[Mu]]]*minkoMetric[[\[Nu],\[Nu]]]*listPs[[i3]][[\[Mu]]]*listPs[[i4]][[\[Nu]]]*
listVBs[[i2]][[subi2]] . pL . gammas[[\[Mu]]] . gammas[[\[Nu]]] . pL . listUs[[i1]],{\[Mu],1,4},{\[Nu],1,4}]]
}
,{i1,listMassless},{i2,listMassive},{subi2,1,2},{i3,listAllParts},{i4,listAllParts}]
]
];
(*/// Compute [p|K L |q] and <p| K L | q> for massive p and q, and on-shell K, L. ///*)
ret=Join[ret,
Flatten[Table[
sqPPsq[ToString[i1][subi1],strMasP[i3],strMasP[i4],ToString[i2][subi2]]->Simplify[Sum[minkoMetric[[\[Mu],\[Mu]]]*minkoMetric[[\[Nu],\[Nu]]]*listPs[[i3]][[\[Mu]]]*listPs[[i4]][[\[Nu]]]*
listVBs[[i1]][[subi1]] . pR . gammas[[\[Mu]]] . gammas[[\[Nu]]] . pR . listUs[[i2]][[subi2]],{\[Mu],1,4},{\[Nu],1,4}]]
,{i1,listMassive},{i2,listMassive},{subi1,1,2},{subi2,1,2},{i3,listAllParts},{i4,listAllParts}]
],
Flatten[Table[
trPPtr[ToString[i1][subi1],strMasP[i3],strMasP[i4],ToString[i2][subi2]]->Simplify[Sum[minkoMetric[[\[Mu],\[Mu]]]*minkoMetric[[\[Nu],\[Nu]]]*listPs[[i3]][[\[Mu]]]*listPs[[i4]][[\[Nu]]]*
listVBs[[i1]][[subi1]] . pL . gammas[[\[Mu]]] . gammas[[\[Nu]]] . pL . listUs[[i2]][[subi2]],{\[Mu],1,4},{\[Nu],1,4}]]
,{i1,listMassive},{i2,listMassive},{subi1,1,2},{subi2,1,2},{i3,listAllParts},{i4,listAllParts}]
]
];
ret
];
randomSpinors[]:=Block[
{ri=RandomInteger[{-10^3,10^3},4],rAng,Angr,rSq,Sqr},
{rAng,rSq}=Partition[ri*ri,2];
Angr=-I*rAng . (PauliMatrix[2]); (*/// I should carefully check these conversions. ///*)
Sqr=I*rSq . PauliMatrix[2];
(*/// Extend to 4D spinors. ///*)
rAng=Join[rAng,{0,0}];
rSq=Join[{0,0},rSq];
Angr=Join[Angr,{0,0}];
Sqr=Join[{0,0},Sqr];
{Angr,rAng,Sqr,rSq}
];

polVectors[kinConfigs_,reempSpinors_]:=Module[
{listVectors,listMassiveVectors,pL,pR,listMasslessVectors,refSpinorMom,ret,Angr,rAng,Sqr,rSq,retM0,
funcPolMassive,funcPolLight},
listVectors=Position[Keys[kinConfigs["p"]],_?((StringContainsQ[ToString[#],"v"])&),1]//Flatten;
pR=(IdentityMatrix[4]+gamma5)/2;
pL=(IdentityMatrix[4]-gamma5)/2;
listMasslessVectors=Select[listVectors,(Simplify[MDot[kinConfigs["p"][[#]],kinConfigs["p"][[#]]]]==0)&];
listMassiveVectors=Complement[listVectors,listMasslessVectors];
(*/// Random Reference spinors. ///*)
{Angr,rAng,Sqr,rSq}=randomSpinors[];
funcPolLight[jj_]:={\[Epsilon]Plus[jj]->(Table[Angr . pL . gammas[[kk]] . pR . kinConfigs["u"][[jj]],{kk,1,4}])/(Sqrt[2]*kinConfigs["vbar"][[jj]] . pL . rAng),
\[Epsilon]Minus[jj]->(Table[kinConfigs["vbar"][[jj]] . pL . gammas[[kk]] . pR . rSq,{kk,1,4}])/(Sqrt[2]*kinConfigs["vbar"][[jj]] . pR . rSq)
};
funcPolMassive[jj_]:={\[Epsilon]Plus[jj]->(tr\[Gamma]Sq[ToString[jj][1],ToString[jj][1]]/(Sqrt[2]Sqrt[FullSimplify[MDot[kinConfigs["p"][[jj]],kinConfigs["p"][[jj]]]]]))/.reempSpinors,\[Epsilon]Minus[jj]->(tr\[Gamma]Sq[ToString[jj][2],ToString[jj][2]]/(Sqrt[2]Sqrt[FullSimplify[MDot[kinConfigs["p"][[jj]],kinConfigs["p"][[jj]]]]]))/.reempSpinors,\[Epsilon]0[jj]->(tr\[Gamma]Sq[ToString[jj][1],ToString[jj][2]]/(2Sqrt[FullSimplify[MDot[kinConfigs["p"][[jj]],kinConfigs["p"][[jj]]]]])+tr\[Gamma]Sq[ToString[jj][2],ToString[jj][1]]/(2Sqrt[FullSimplify[MDot[kinConfigs["p"][[jj]],kinConfigs["p"][[jj]]]]]))/.reempSpinors};
ret=Table[If[MemberQ[listMassiveVectors,jj],funcPolMassive[jj],funcPolLight[jj]],{jj,listVectors}];
ret
];
momReplacement[kinConfigs_]:=Module[{listPs,numPart,ret},
listPs=kinConfigs["p"];
numPart=Length[listPs];
ret=Flatten[Table[ToExpression["p"<>ToString[ii]][jj]->listPs[[ii,jj]],{ii,1,numPart},{jj,1,4}]]
];
replacePolVecs[pol_,polVecEval_]:=Piecewise[{{
{Global`epsp1[i_]:>(\[Epsilon]Plus[1]/.polVecEval)[[i]],Global`epsp2[i_]:>(\[Epsilon]Plus[2]/.polVecEval)[[i]]}
,pol=="++"}
}];
eqToMatch[ampOS_,ampSMEFT_,pol_,nf_,nV_,nS_,masses_:0]:=Block[{phSpPt,phSpPtSpinProd,phSpMom,phSpPolVec},
phSpPt=generateKinematics[nf,nV,nS,masses];
phSpPtSpinProd=reempSpinProd[phSpPt];
phSpMom=momReplacement[phSpPt];
phSpPolVec=replacePolVecs[pol,Flatten[polVectors[phSpPt,phSpPtSpinProd]]];
((ampOS/.phSpPtSpinProd/.phSpMom)-(ampSMEFT/.phSpPolVec/.phSpMom))
];

End[];
EndPackage[];
