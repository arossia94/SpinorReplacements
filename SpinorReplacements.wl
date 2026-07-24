(* ::Package:: *)

(* ::Package:: *)
(* SpinorReplacements Package *)
(* Combines mosca KinematicSubstitution with custom spinor replacement functions *)


BeginPackage["SpinorReplacements`"];
Print["SpinorReplacements: numerical evaluation of massive and massless helicity spinors.\n"];
Print["Version: 0.19"];
Print["Date: 24/07/2026"];
Print["Author: Alejo N. Rossia"];
Print["Affiliations: Universita di Padova"];
(* Load the external packages needed *)
$ContextPath = Join[{"SpinorReplacements`"}, $ContextPath];
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
sqBrKt::usage = "Square spinor bracket [i|j].";
trBrKt::usage = "Triangular spinor bracket \:27e8i|j\[RightAngleBracket].";
sq\[Gamma]Tr::usage = "[i|\[Gamma]^\[Mu]|j\[RightAngleBracket].";
tr\[Gamma]Sq::usage = "\:27e8i|\[Gamma]^\[Mu]|j].";
sqPPsq::usage = "[i|p q|j].";
trPPtr::usage = "\:27e8i|p q|j\[RightAngleBracket].";
sqPtr::usage = "[i|p|j\[RightAngleBracket].";
trPsq::usage = "\:27e8i|p|j].";

(* Polarization symbols *)
(*\[Epsilon]Plus::usage = "Positive helicity polarization vector.";
\[Epsilon]Minus::usage = "Negative helicity polarization vector.";
\[Epsilon]0::usage = "Longitudinal polarization vector.";*)

(* Mass symbols for massive particles *)
masP::usage = "Mass parameter for massive particle.";

Begin["`Private`"];

(* ========================================================================= *)
(* PART 1: KinematicSubstitution from mosca (modified version)              *)
(* ========================================================================= *)

(* Load mosca's NumericalKinematics *)
(*Get["SpinorReplacements`ExternalPackages`NumericalKinematics`"];*)
Get["SpinorReplacements`ExternalPackages`KinematicSubstitution`"];
Get["SpinorReplacements`ExternalPackages`LCeps4eval`"];
generateKinematics[nF_,nV_,nS_,masses_:0]:=KinematicConfigurations[nF,nV,nS,masses];


(* ========================================================================= *)
(* PART 2: Custom Spinor Replacement Functions                               *)
(* ========================================================================= *)
reempSpinProd[genKin_,rndSpinors_:randomSpinors[]]:=Module[{listUs,listVBs,listPs,pR,pL,listAllParts,listMasses,listMassless,listMassive,ret,strMasP,minkoMetric,Angr,rAng,Sqr,rSq},
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
ret=DeleteCases[Flatten[Table[If[i1!=i2,{sqBrKt[ToString[i1],ToString[i2]]->listVBs[[i1]] . pR . listUs[[i2]],trBrKt[ToString[i1],ToString[i2]]->listVBs[[i1]] . pL . listUs[[i2]]},"0"],{i1,listMassless},{i2,listMassless}]],a_/;a==="0"];
(*/// Compute [p|q], <p|q>, [q|p], <q|p> with p massless and q massive.///*)
ret=Join[ret,
Flatten[Table[{trBrKt[ToString[i1],ToString[i2][subi2]]->listVBs[[i1]] . pL . listUs[[i2]][[subi2]],trBrKt[ToString[i2][subi2],ToString[i1]]->
listVBs[[i2]][[subi2]] . pL . listUs[[i1]], sqBrKt[ToString[i1],ToString[i2][subi2]]->listVBs[[i1]] . pR . listUs[[i2]][[subi2]], sqBrKt[ToString[i2][subi2],ToString[i1]]->
listVBs[[i2]][[subi2]] . pR . listUs[[i1]]},{i1,listMassless},{i2,listMassive},{subi2,1,2}]]];
(*/// Compute [p|q], <p|q>, [q|p], <q|p> with p and q massive.///*)
ret=Join[ret,
Flatten[Table[{trBrKt[ToString[i1][subi1],ToString[i2][subi2]]->Simplify[listVBs[[i1]][[subi1]] . pL . listUs[[i2]][[subi2]]],sqBrKt[ToString[i1][subi1],ToString[i2][subi2]]->Simplify[listVBs[[i1]][[subi1]] . pR . listUs[[i2]][[subi2]]]},{i1,listMassive},{i2,listMassive},{subi1,1,2},{subi2,1,2}]]];
(*/// Compute <p|\[Gamma]^\[Mu]|q] and <q|\[Gamma]^\[Mu]|p] for massless momenta. ///*);
ret=Join[ret,
Flatten[Table[{sq\[Gamma]Tr[ToString[i1],ToString[i2]]->Table[listVBs[[i1]] . pR . gammas[[jj]] . pL . listUs[[i2]],{jj,1,4}],tr\[Gamma]Sq[ToString[i1],ToString[i2]]->Table[listVBs[[i1]] . pL . gammas[[jj]] . pR . listUs[[i2]],{jj,1,4}]},{i1,listMassless},{i2,listMassless}]]
];
(*/// Compute <p|\[Gamma]^\[Mu]|q] and <q|\[Gamma]^\[Mu]|p] for q massive and p massless. ///*)
ret=Join[ret,
Flatten[Table[{sq\[Gamma]Tr[ToString[i1],ToString[i2][subi2]]->Table[listVBs[[i1]] . pR . gammas[[jj]] . pL . listUs[[i2]][[subi2]],{jj,1,4}],tr\[Gamma]Sq[ToString[i1],ToString[i2][subi2]]->Table[listVBs[[i1]] . pL . gammas[[jj]] . pR . listUs[[i2]][[subi2]],{jj,1,4}]},{i1,listMassless},{i2,listMassive},{subi2,1,2}]],
Flatten[Table[{tr\[Gamma]Sq[ToString[i1][subi1],ToString[i2]]->Table[listVBs[[i1]][[subi1]] . pL . gammas[[jj]] . pR . listUs[[i2]],{jj,1,4}],sq\[Gamma]Tr[ToString[i1][subi1],ToString[i2]]->Table[listVBs[[i1]][[subi1]] . pR . gammas[[jj]] . pL . listUs[[i2]],{jj,1,4}]},{i1,listMassive},{i2,listMassless},{subi1,1,2}]]
];
(*/// Compute <p|\[Gamma]^\[Mu]|q] and <q|\[Gamma]^\[Mu]|p] for q and p massive. ///*)
ret=Join[ret,
Flatten[Table[{sq\[Gamma]Tr[ToString[i1][subi1],ToString[i2][subi2]]->Table[listVBs[[i1]][[subi1]] . pR . gammas[[jj]] . pL . listUs[[i2]][[subi2]],{jj,1,4}],tr\[Gamma]Sq[ToString[i1][subi1],ToString[i2][subi2]]->Table[listVBs[[i1]][[subi1]] . pL . gammas[[jj]] . pR . listUs[[i2]][[subi2]],{jj,1,4}]},{i1,listMassive},{i2,listMassive},{subi1,1,2},{subi2,1,2}]]
];
(*/// Compute <p|K|q] and <q|K|p] for massless p,q and general on-shell K. ///*)
ret=Join[ret,
Flatten[Table[{
trPsq[ToString[i1],strMasP[i3],ToString[i2]]->Simplify[MDot[listPs[[i3]],
Table[listVBs[[i1]] . pL . gammas[[jj]] . pR . listUs[[i2]],{jj,1,4}]]],
sqPtr[ToString[i1],strMasP[i3],ToString[i2]]->Simplify[MDot[listPs[[i3]],
Table[listVBs[[i1]] . pR . gammas[[jj]] . pL . listUs[[i2]],{jj,1,4}]]]
}
,{i1,listMassless},{i2,listMassless},{i3,listAllParts}]
]];
(*/// Compute <p|K|q] and <q|K|p] for massless p, massive q and general on-shell K. ///*)
ret=Join[ret,
Flatten[Table[
{trPsq[ToString[i1],strMasP[i3],ToString[i2][subi2]]->Simplify[MDot[listPs[[i3]],
Table[listVBs[[i1]] . pL . gammas[[jj]] . pR . listUs[[i2]][[subi2]],{jj,1,4}]]],
trPsq[ToString[i2][subi2],strMasP[i3],ToString[i1]]->Simplify[MDot[listPs[[i3]],
Table[listVBs[[i2]][[subi2]] . pL . gammas[[jj]] . pR . listUs[[i1]],{jj,1,4}]]],
sqPtr[ToString[i1],strMasP[i3],ToString[i2][subi2]]->Simplify[MDot[listPs[[i3]],
Table[listVBs[[i1]] . pR . gammas[[jj]] . pL . listUs[[i2]][[subi2]],{jj,1,4}]]],
sqPtr[ToString[i2][subi2],strMasP[i3],ToString[i1]]->Simplify[MDot[listPs[[i3]],
Table[listVBs[[i2]][[subi2]] . pR . gammas[[jj]] . pL . listUs[[i1]],{jj,1,4}]]]
},{i1,listMassless},{i2,listMassive},{subi2,1,2},{i3,listAllParts}]
]];
(*/// Compute <p|K|q] and <q|K|p] for massive p and q and general on-shell K. ///*)
ret=Join[ret,
Flatten[Table[{
trPsq[ToString[i1][subi1],strMasP[i3],ToString[i2][subi2]]->Simplify[MDot[listPs[[i3]],
Table[listVBs[[i1]][[subi1]] . pL . gammas[[jj]] . pR . listUs[[i2]][[subi2]],{jj,1,4}]]],
sqPtr[ToString[i1][subi1],strMasP[i3],ToString[i2][subi2]]->Simplify[MDot[listPs[[i3]],
Table[listVBs[[i1]][[subi1]] . pR . gammas[[jj]] . pL . listUs[[i2]][[subi2]],{jj,1,4}]]]}
,{i1,listMassive},{i2,listMassive},{subi1,1,2},{subi2,1,2},{i3,listAllParts}]]
];
(*/// Compute [p|K L |q] and <p| K L | q> for massless p,q and on-shell K, L. ///*)
ret=Join[ret,
Flatten[Table[
{sqPPsq[ToString[i1],strMasP[i3],strMasP[i4],ToString[i2]]->Simplify[Sum[minkoMetric[[\[Mu],\[Mu]]]*minkoMetric[[\[Nu],\[Nu]]]*listPs[[i3]][[\[Mu]]]*listPs[[i4]][[\[Nu]]]*
listVBs[[i1]] . pR . gammas[[\[Mu]]] . gammas[[\[Nu]]] . pR . listUs[[i2]],{\[Mu],1,4},{\[Nu],1,4}]],
trPPtr[ToString[i1],strMasP[i3],strMasP[i4],ToString[i2]]->Simplify[Sum[minkoMetric[[\[Mu],\[Mu]]]*minkoMetric[[\[Nu],\[Nu]]]*listPs[[i3]][[\[Mu]]]*listPs[[i4]][[\[Nu]]]*
listVBs[[i1]] . pL . gammas[[\[Mu]]] . gammas[[\[Nu]]] . pL . listUs[[i2]],{\[Mu],1,4},{\[Nu],1,4}]]}
,{i1,listMassless},{i2,listMassless},{i3,listAllParts},{i4,listAllParts}]]];
(*/// Compute [p|K L |q] and <p| K L | q> for massless p, massive q and on-shell K, L. ///*)
ret=Join[ret,
Flatten[Table[{
sqPPsq[ToString[i1],strMasP[i3],strMasP[i4],ToString[i2][subi2]]->Simplify[Sum[minkoMetric[[\[Mu],\[Mu]]]*minkoMetric[[\[Nu],\[Nu]]]*listPs[[i3]][[\[Mu]]]*listPs[[i4]][[\[Nu]]]*
listVBs[[i1]] . pR . gammas[[\[Mu]]] . gammas[[\[Nu]]] . pR . listUs[[i2]][[subi2]],{\[Mu],1,4},{\[Nu],1,4}]],
sqPPsq[ToString[i2][subi2],strMasP[i3],strMasP[i4],ToString[i1]]->Simplify[Sum[minkoMetric[[\[Mu],\[Mu]]]*minkoMetric[[\[Nu],\[Nu]]]*listPs[[i3]][[\[Mu]]]*listPs[[i4]][[\[Nu]]]*
listVBs[[i2]][[subi2]] . pR . gammas[[\[Mu]]] . gammas[[\[Nu]]] . pR . listUs[[i1]],{\[Mu],1,4},{\[Nu],1,4}]],
trPPtr[ToString[i1],strMasP[i3],strMasP[i4],ToString[i2][subi2]]->Simplify[Sum[minkoMetric[[\[Mu],\[Mu]]]*minkoMetric[[\[Nu],\[Nu]]]*listPs[[i3]][[\[Mu]]]*listPs[[i4]][[\[Nu]]]*
listVBs[[i1]] . pL . gammas[[\[Mu]]] . gammas[[\[Nu]]] . pL . listUs[[i2]][[subi2]],{\[Mu],1,4},{\[Nu],1,4}]],
trPPtr[ToString[i2][subi2],strMasP[i3],strMasP[i4],ToString[i1]]->Simplify[Sum[minkoMetric[[\[Mu],\[Mu]]]*minkoMetric[[\[Nu],\[Nu]]]*listPs[[i3]][[\[Mu]]]*listPs[[i4]][[\[Nu]]]*
listVBs[[i2]][[subi2]] . pL . gammas[[\[Mu]]] . gammas[[\[Nu]]] . pL . listUs[[i1]],{\[Mu],1,4},{\[Nu],1,4}]]},
{i1,listMassless},{i2,listMassive},{subi2,1,2},{i3,listAllParts},{i4,listAllParts}]
]];
(*/// Compute [p|K L |q] and <p| K L | q> for massive p and q, and on-shell K, L. ///*)
ret=Join[ret,
Flatten[Table[
{sqPPsq[ToString[i1][subi1],strMasP[i3],strMasP[i4],ToString[i2][subi2]]->Simplify[Sum[minkoMetric[[\[Mu],\[Mu]]]*minkoMetric[[\[Nu],\[Nu]]]*listPs[[i3]][[\[Mu]]]*listPs[[i4]][[\[Nu]]]*
listVBs[[i1]][[subi1]] . pR . gammas[[\[Mu]]] . gammas[[\[Nu]]] . pR . listUs[[i2]][[subi2]],{\[Mu],1,4},{\[Nu],1,4}]],
trPPtr[ToString[i1][subi1],strMasP[i3],strMasP[i4],ToString[i2][subi2]]->Simplify[Sum[minkoMetric[[\[Mu],\[Mu]]]*minkoMetric[[\[Nu],\[Nu]]]*listPs[[i3]][[\[Mu]]]*listPs[[i4]][[\[Nu]]]*
listVBs[[i1]][[subi1]] . pL . gammas[[\[Mu]]] . gammas[[\[Nu]]] . pL . listUs[[i2]][[subi2]],{\[Mu],1,4},{\[Nu],1,4}]]}
,{i1,listMassive},{i2,listMassive},{subi1,1,2},{subi2,1,2},{i3,listAllParts},{i4,listAllParts}]]
];
(*/// Comput product spinors with one random reference spinor. ///*)
(*/// Define the random spinors to use. ///*);
{Angr,rAng,Sqr,rSq}=rndSpinors;
(*/// Compute product spinors for one random reference and one massless spinor. ///*);
ret=Join[ret,
Flatten[Table[{sqBrKt[ToString[i1],"ref"]->listVBs[[i1]] . pR . rSq,sqBrKt["ref",ToString[i1]]->Sqr . pR . listUs[[i1]],trBrKt[ToString[i1],"ref"]->listVBs[[i1]] . pL . rAng,trBrKt["ref",ToString[i1]]->Angr . pL . listUs[[i1]]},{i1,listMassless}]]];
(*/// Compute [p|q], <p|q>, [q|p], <q|p> with p=random reference and q massive.///*)
ret=Join[ret,
Flatten[Table[{trBrKt["ref",ToString[i2][subi2]]->Angr . pL . listUs[[i2]][[subi2]],trBrKt[ToString[i2][subi2],"ref"]->
listVBs[[i2]][[subi2]] . pL . rAng,
sqBrKt["ref",ToString[i2][subi2]]->Sqr . pR . listUs[[i2]][[subi2]],sqBrKt[ToString[i2][subi2],"ref"]->
listVBs[[i2]][[subi2]] . pR . rSq},
{i2,listMassive},{subi2,1,2}]]
];
(*/// Compute <p|K|q] and <q|K|p] for p=random reference spinor, massive q, and general on-shell K. ///*)
ret=Join[ret,
Flatten[Table[{
trPsq["ref",strMasP[i3],ToString[i2][subi2]]->Simplify[MDot[listPs[[i3]],
Table[Angr . pL . gammas[[jj]] . pR . listUs[[i2]][[subi2]],{jj,1,4}]]],
sqPtr["ref",strMasP[i3],ToString[i2][subi2]]->Simplify[MDot[listPs[[i3]],
Table[Sqr . pR . gammas[[jj]] . pL . listUs[[i2]][[subi2]],{jj,1,4}]]]
},
{i2,listMassive},{subi2,1,2},{i3,listAllParts}]],
Flatten[Table[{
trPsq[ToString[i1][subi1],strMasP[i3],"ref"]->Simplify[MDot[listPs[[i3]],
Table[listVBs[[i1]][[subi1]] . pL . gammas[[jj]] . pR . rSq,{jj,1,4}]]],
sqPtr[ToString[i1][subi1],strMasP[i3],"ref"]->Simplify[MDot[listPs[[i3]],
Table[listVBs[[i1]][[subi1]] . pR . gammas[[jj]] . pL . rAng,{jj,1,4}]]]}
,{i1,listMassive},{subi1,1,2},{i3,listAllParts}]]
];
(*/// Compute <p|K|p] for p=random reference spinor, and general on-shell K. ///*)
ret=Join[ret,
Flatten[Table[
trPsq["ref",strMasP[i3],"ref"]->Simplify[MDot[listPs[[i3]],
Table[Angr . pL . gammas[[jj]] . pR . rSq,{jj,1,4}]]]
,{i3,listAllParts}]]];
ret
];
randomSpinors[]:=Block[
{ri=RandomInteger[{-10^3,10^3},4],rAng,Angr,rSq,Sqr},
{rAng,rSq}=Partition[ri*ri,2];
Angr=I*rAng . (PauliMatrix[2]);
Sqr=-I*rSq . PauliMatrix[2];
(*/// Extend to 4D spinors. ///*)
rAng=Join[rAng,{0,0}];
rSq=Join[{0,0},rSq];
Angr=Join[Angr,{0,0}];
Sqr=Join[{0,0},Sqr];
{Angr,rAng,Sqr,rSq}
];
polVectors[kinConfigs_,reempSpinors_,rndSpinors_:randomSpinors[]]:=Module[
{listVectors,listMassiveVectors,pL,pR,listMasslessVectors,refSpinorMom,ret,Angr,rAng,Sqr,rSq,retM0,
funcPolMassive,funcPolLight},
listVectors=Position[Keys[kinConfigs["p"]],_?((StringContainsQ[ToString[#],"v"])&),1]//Flatten;
pR=(IdentityMatrix[4]+gamma5)/2;
pL=(IdentityMatrix[4]-gamma5)/2;
listMasslessVectors=Select[listVectors,(Simplify[MDot[kinConfigs["p"][[#]],kinConfigs["p"][[#]]]]==0)&];
listMassiveVectors=Complement[listVectors,listMasslessVectors];
(*/// Random Reference spinors. ///*)
{Angr,rAng,Sqr,rSq}=rndSpinors;
(*funcPolLight[jj_]:={\[Epsilon]Plus[jj]->kinConfigs["e+"][[jj]],
\[Epsilon]Minus[jj]->kinConfigs["e-"][[jj]]};*)
(*funcPolLight[jj_]:={\[Epsilon]Plus[jj]->({(k[1]-\[ImaginaryI] k[3])/(Sqrt[2] (k[0]+k[2])),1/Sqrt[2],-((k[1]-\[ImaginaryI] k[3])/(Sqrt[2] (k[0]+k[2]))),-(\[ImaginaryI]/Sqrt[2])})/.{k[0]->(kinConfigs["p"][[jj]])[[1]],k[1]->(kinConfigs["p"][[jj]])[[2]],k[2]->(kinConfigs["p"][[jj]])[[3]],k[3]->(kinConfigs["p"][[jj]])[[4]]},
\[Epsilon]Minus[jj]->({-((k[1]+\[ImaginaryI] k[3])/(Sqrt[2] (k[0]+k[2]))),-(1/Sqrt[2]),(k[1]+\[ImaginaryI] k[3])/(Sqrt[2] (k[0]+k[2])),-(\[ImaginaryI]/Sqrt[2])})/.{k[0]->(kinConfigs["p"][[jj]])[[1]],k[1]->(kinConfigs["p"][[jj]])[[2]],k[2]->(kinConfigs["p"][[jj]])[[3]],k[3]->(kinConfigs["p"][[jj]])[[4]]}};
*)
funcPolLight[jj_]:={\[Epsilon]Plus[jj]->(Table[Angr . pL . gammas[[kk]] . pR . kinConfigs["u"][[jj]],{kk,1,4}])/(Sqrt[2]*kinConfigs["vbar"][[jj]] . pL . rAng),
\[Epsilon]Minus[jj]->(Table[kinConfigs["vbar"][[jj]] . pL . gammas[[kk]] . pR . rSq,{kk,1,4}])/(Sqrt[2]*kinConfigs["vbar"][[jj]] . pR . rSq)};
funcPolMassive[jj_]:={\[Epsilon]Plus[jj]->(tr\[Gamma]Sq[ToString[jj][1],ToString[jj][1]]/(Sqrt[2]Sqrt[FullSimplify[MDot[kinConfigs["p"][[jj]],kinConfigs["p"][[jj]]]]]))/.reempSpinors,
\[Epsilon]Minus[jj]->(tr\[Gamma]Sq[ToString[jj][2],ToString[jj][2]]/(Sqrt[2]Sqrt[FullSimplify[MDot[kinConfigs["p"][[jj]],kinConfigs["p"][[jj]]]]]))/.reempSpinors,
\[Epsilon]0[jj]->(tr\[Gamma]Sq[ToString[jj][1],ToString[jj][2]]/(2 Sqrt[FullSimplify[MDot[kinConfigs["p"][[jj]],kinConfigs["p"][[jj]]]]])+tr\[Gamma]Sq[ToString[jj][2],ToString[jj][1]]/(2 Sqrt[FullSimplify[MDot[kinConfigs["p"][[jj]],kinConfigs["p"][[jj]]]]]))/.reempSpinors};
ret=Table[If[MemberQ[listMassiveVectors,jj],funcPolMassive[jj],funcPolLight[jj]],{jj,listVectors}];
ret];
momReplacement[kinConfigs_]:=Module[{listPs,numPart,ret},
listPs=kinConfigs["p"];
numPart=Length[listPs];
ret=Flatten[Table[ToExpression["p"<>ToString[ii]][jj]->listPs[[ii,jj]],{ii,1,numPart},{jj,1,4}]]
];
replacePolVecs[pol_,polVecEval_]:=Block[{numVecs,numFerms},
numVecs=StringLength[pol];
numFerms=polVecEval[[1,1,1]]-1;
Table[With[{kk=kk,g=kk+numFerms},
RuleDelayed[ToExpression["Global`epsp"<>ToString[kk]][i_],
(Piecewise[{{\[Epsilon]Plus,StringTake[pol,{kk}]=="+"},{\[Epsilon]Minus,StringTake[pol,{kk}]=="-"},
{\[Epsilon]0,StringTake[pol,{kk}]=="0"}}][g]/.polVecEval)[[i]]]],{kk,1,numVecs}]
];
eqToMatch[ampOS_,ampSMEFT_,pol_,nf_,nV_,nS_,masses_:0,rndSpinors_:Automatic]:=Block[
{phSpPt,phSpPtSpinProd,phSpMom,phSpPolVec,rndSpinorSet,ret,gmet,preRepLC,repLC},
rndSpinorSet=If[rndSpinors===Automatic,randomSpinors[],rndSpinors];
phSpPt=generateKinematics[nf,nV,nS,masses];
phSpPtSpinProd=reempSpinProd[phSpPt,rndSpinorSet];
phSpMom=momReplacement[phSpPt];
phSpPolVec=replacePolVecs[pol,Flatten[polVectors[phSpPt,phSpPtSpinProd,rndSpinorSet]]];
ret=((ampOS/.phSpPtSpinProd/.phSpPolVec/.phSpMom)-(ampSMEFT/.phSpPolVec/.phSpMom));
If[MemberQ[Variables[ret],SpinorReplacements`LCeps4[__]],
gmet=DiagonalMatrix[{1,-1,-1,-1}];
preRepLC={SpinorReplacements`eps[i_]:>ToExpression["Global`epsp"<>ToString[i]],SpinorReplacements`pmom[i_]:>ToExpression["p"<>ToString[i]]};
repLC={SpinorReplacements`LCeps4[A_,B_,C_,D_]:>Sum[Normal[LeviCivitaTensor[4]][[m, n, r, s]] (A/.preRepLC)[m] (B/.preRepLC)[n] (C/.preRepLC)[r] (D/.preRepLC)[s] gmet[[m,m]] gmet[[n,n]] gmet[[r,r]] gmet[[s,s]], {m,4},{n,4},{r,4},{s,4}]};
ret=ret/.repLC/.phSpPolVec/.phSpMom;];
ret
];
End[];
EndPackage[];
