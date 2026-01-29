(* ::Package:: *)

BeginPackage["KinematicSubstitution`"];


Rules::usage = "Rules[n,p,x] returns a list of n"
rules`Pair::usage = "jhds"
rules`k::usage = "momentum"
rules`e::usage = "polarizations"
mH
KinematicConfigurations
MDot
pslash
gammas
gamma5
SustMomenta
SustMomentaSemiOptimized
SustMomentaOptimized
SustMomentaOptimized2
SustMomentaRules
ReplaceKinematics
i
j


Begin["`Private`"]


Get["SpinorReplacements`ExternalPackages`NumericalKinematics`"]

Mdot[p1_List,p2_List]:=p1 . DiagonalMatrix[{1,-1,-1,-1}] . p2;
eps=I PauliMatrix[2];
\[Sigma]s={IdentityMatrix[2],{{0,1},{1,0}},{{0,-I},{I,0}},{{1,0},{0,-1}}};
sigmamuup=Join[{IdentityMatrix[2]},Table[PauliMatrix[i],{i,3}]];
sigmabarmuup=Join[{IdentityMatrix[2]},-Table[PauliMatrix[i],{i,3}]];
gammas=Table[DiagonalMatrix[{0,0,0,0}],{i,4}];
Do[gammas[[i]][[1;;2,3;;4]]=sigmamuup[[i]];gammas[[i]][[3;;4,1;;2]]=sigmabarmuup[[i]],{i,4}];
gamma5=DiagonalMatrix[{-1,-1,1,1}];
pslash[pmu_]:=pmu[[1]]gammas[[1]]-Sum[pmu[[i]]gammas[[i]],{i,2,4}];
dotprule={Dot[a_+b_,c_]->Dot[a,c]+Dot[b,c],Dot[a_,b_+c_]->Dot[a,b]+Dot[a,c],Dot[-a_,b_]->-Dot[a,b],Dot[a_,-b_]->-Dot[a,b],gam[a___,-b_,c___]->-gam[a,b,c],Mom[-p_,mumu2_]->-Mom[p,mumu2]};

pfun[i_]:=ToExpression["p"<>ToString[i]]
pmu[j_]:=1/2 Table[Tr[\[Sigma]s[[i]] . NMomentum[ToExpression["p"<>ToString[j]]]],{i,1,4}]//FullSimplify


GenerateGeneralKinematics[mlist_]:=Module[{masslessparticles=Flatten[Position[mlist,0]],massiveparticles,massivemomenta,allmomenta,numspinors},
	massiveparticles=Complement[Range[Length[mlist]],masslessparticles];
	massivemomenta=pfun/@massiveparticles;
	allmomenta=pfun/@Range[Length[mlist]];
	ClearKinematics[];
	Off[GenerateKinematics::NonSquareMasses];
	Off[Part::partw];
	GenerateKinematics[allmomenta,MassiveParticles->massivemomenta,Masses->MapThread[Rule,{massivemomenta,DeleteCases[mlist*mlist,0]}],Echos->False,HighestNumber->10];
	positivemasses=DeleteCases[Table[mlist[[jj]]>0,{jj,Length[mlist]}],False];
	]
	
uspinall[j_]:=Block[{res},
	If[FullSimplify[Mdot[pmu[j],pmu[j]]]===0,
	res={Join[eps . NSpinorDottedML[pfun[j]],{0,0}],Join[{0,0},NSpinorUndottedML[pfun[j]]]},
	res=Table[Join[eps . NSpinorDottedMV[pfun[j],i],NSpinorUndottedMV[pfun[j],i]],{i,2}]];
	FullSimplify[res,positivemasses]
	]
	
	
vbspinall[j_]:=Block[{res},
	If[FullSimplify[Mdot[pmu[j],pmu[j]]]===0,
	res={Join[eps . NSpinorUndottedML[pfun[j]],{0,0}] . gammas[[1]],Join[{0,0},NSpinorDottedML[pfun[j]]] . gammas[[1]]},
	res=Table[Join[-NSpinorUndottedMV[pfun[j],i] . eps,NSpinorDottedMV[pfun[j],i]] . gammas[[1]],{i,2}]];
	FullSimplify[res,positivemasses]
	]



Rules[masslist_,nFermions_,nVectors_,nScalars_]:=Module[{allpmus,l,n},

	nparts=nFermions+nVectors+nScalars;
	GenerateGeneralKinematics[masslist];

	(*Momenta*)
	allpmus={Table[pmu[i],{i,nparts}]}/.a->0;
	ps=Flatten[allpmus,1];
	(*ps[[-1]]=-ps[[-1]];*)
	
	(*Spinors*)
	uspinors=Table[uspinall[i][[1]]+uspinall[i][[2]],{i,1,nFermions}];
	vbspinors=Table[vbspinall[i][[1]]+vbspinall[i][[2]],{i,1,nFermions}];
	
	epsmu[j_]:=Block[{ri=RandomInteger[{-10^3,10^3},4],rang,rsq,angr,sqr,pang,psq,angp,sqp},
	{rang,rsq}=Partition[ri*ri,2];
	angr=-rang . eps;
	sqr=rsq . eps;
	pang=eps . NSpinorDottedML[pfun[j]];
	psq=NSpinorUndottedML[pfun[j]];
	angp=-pang . eps;
	sqp=psq . eps;
	FullSimplify[{Table[angr . sigmamuup[[mu]] . psq,{mu,1,4}]/Sqrt[2]/(angr . pang),Table[angp . sigmamuup[[mu]] . rsq,{mu,4}]/Sqrt[2]/(sqp . rsq)},positivemasses]];
	
	(*Polarizations*)
	eplus=Table[epsmu[i][[1]],{i,nFermions+1,nFermions+nVectors}];
	eminus=Table[epsmu[i][[2]],{i,nFermions+1,nFermions+nVectors}];
	
	Return[{ps,uspinors,vbspinors,eplus,eminus}];
];


KinematicConfigurations[nFermions_,nVectors_,nScalars_,masses_:0]:=Module[{allpmus,l,n},

	nparts=nFermions+nVectors+nScalars;
	
	If[Head@masses=!=List
	,
	GenerateGeneralKinematics[Table[masses,nparts]];
	,
	GenerateGeneralKinematics[masses];
	];
	
	(*Momenta*)
	allpmus={Table[pmu[i],{i,nparts}]}/.a->0;
	ps=Flatten[allpmus,1];
	(*ps[[-1]]=-ps[[-1]];*)
		
	(*Spinors*)	
	uspinors=Table[{uspinall[i][[1]],uspinall[i][[2]]},{i,1,nFermions+nVectors+nScalars}];
	vbspinors=Table[{vbspinall[i][[1]],vbspinall[i][[2]]},{i,1,nFermions+nVectors+nScalars}];
	
	Do[If[FullSimplify[MDot[ps[[i]],ps[[i]]]]===0,
	uspinors[[i]]=Total[uspinors[[i]]];
	vbspinors[[i]]=Total[vbspinors[[i]]];
	];
	,{i,1,nFermions+nVectors+nScalars}];
	
	epsmu[j_]:=Block[{ri=RandomInteger[{-10^3,10^3},4],rang,rsq,angr,sqr,pang,psq,angp,sqp},
	{rang,rsq}=Partition[ri*ri,2];
	angr=-rang . eps;
	sqr=rsq . eps;
	pang=eps . NSpinorDottedML[pfun[j]];
	psq=NSpinorUndottedML[pfun[j]];
	angp=-pang . eps;
	sqp=psq . eps;
	FullSimplify[{Table[angr . sigmamuup[[mu]] . psq,{mu,1,4}]/(angr . pang),Table[angp . sigmamuup[[mu]] . rsq,{mu,4}]/2/(sqp . rsq)},positivemasses]];
	
	(*Polarizations*)
	eplus=Table[epsmu[i][[1]],{i,nFermions+1,nFermions+nVectors}];
	eminus=Table[epsmu[i][[2]],{i,nFermions+1,nFermions+nVectors}];
	
	(*Converting into associations*)
	With[{keys=Join@@{Symbol["f"<>ToString@#]&/@Range[nFermions],Symbol["v"<>ToString@#]&/@Range[nVectors],Symbol["s"<>ToString@#]&/@Range[nScalars]}},
		ps = AssociationThread[keys,ps];
	];
	
	With[{keys=Join@@{Symbol["f"<>ToString@#]&/@Range[nFermions],Symbol["v"<>ToString@#]&/@Range[nVectors],Symbol["s"<>ToString@#]&/@Range[nScalars]}},
		uspinors = AssociationThread[keys,uspinors];
		vbspinors = AssociationThread[keys,vbspinors];
	];
	
	With[{keys=Symbol["v"<>ToString@#]&/@Range[nVectors]},
		eplus = AssociationThread[keys,eplus];
		eminus = AssociationThread[keys,eminus];
	];
	
	<|"p"->ps,"u"->uspinors,"vbar"->vbspinors,"e+"->eplus,"e-"->eminus|>
];


(* ::Subsection:: *)
(*Generation and substitution of random momenta*)


eps4= I LeviCivitaTensor[4];
changeparity:={{0,0,1,0},{0,0,0,1},{1,0,0,0},{0,1,0,0}}
\[Sigma]s={IdentityMatrix[2],{{0,1},{1,0}},{{0,-I},{I,0}},{{1,0},{0,-1}}};
sigmamuup=Join[{IdentityMatrix[2]},Table[PauliMatrix[i],{i,3}]];
sigmabarmuup=Join[{IdentityMatrix[2]},-Table[PauliMatrix[i],{i,3}]];
gammas=Table[DiagonalMatrix[{0,0,0,0}],{i,4}];

Do[gammas[[i]][[1;;2,3;;4]]=sigmamuup[[i]];gammas[[i]][[3;;4,1;;2]]=sigmabarmuup[[i]],{i,4}];
gamma5=DiagonalMatrix[{-1,-1,1,1}];
pslash[pmu_List]:=pmu[[1]]gammas[[1]]-Sum[pmu[[i]]gammas[[i]],{i,2,4}];
MDot[a_List,b_List] := a[[1]]b[[1]]-a[[2;;-1]] . b[[2;;-1]];
EpsEval[x_List,y_List,t_List,w_List]:=Sum[eps4[[\[Mu],\[Nu],\[Rho],\[Sigma]]]x[[\[Mu]]]y[[\[Nu]]]t[[\[Rho]]]w[[\[Sigma]]],{\[Mu],1,4},{\[Nu],1,4},{\[Rho],1,4},{\[Sigma],1,4}];
ProjectorSust:={DiracGamma[6]->(IdentityMatrix[4]+gamma5)/2,DiracGamma[7]->(IdentityMatrix[4]-gamma5)/2};

doGammas[exp_]:=Module[{exp2=If[Head[exp]===Plus,List@@exp,{exp}], exp3,exptot=0},
Do[
exp3=exp2[[n]]/.DiracGamma[LorentzIndex[a_]]:>gammasb[a];
indexList=DeleteDuplicates[Cases[exp3,gammasb[x_]:>x,Infinity]];
indexListsust=Table[Unique[],{i,Length[indexList]}];
exp3=exp3/.MapThread[Rule,{indexList,indexListsust}];
exp3=If[Length[indexList]>0,Sum[exp3,##]&@@Table[{indexListsust[[k]],1,4},{k,1,Length[indexListsust]}]/.Flatten[{gammasb[1]->gammas[[1]],Table[gammasb[i]->I gammas[[i]],{i,2,4}]}],exp3];
exptot=exptot+exp3,
{n,1,Length[exp2]}];
Return[exptot]
]


SustMomenta[amp_,fermions_,vectors_,scalars_,mlist_] := SustMomenta[{amp},fermions,vectors,scalars,mlist]

SustMomenta[amp_List,fermions_,vectors_,scalars_,mlist_]:=Module[{eList,ecList,ampList,ampmodIR,ampmodUV,randomValues,\[Epsilon],\[Epsilon]c},
randomValues=Rules[mlist,fermions,vectors,scalars];
eList=Tuples[Table[{randomValues[[4]][[i]],randomValues[[5]][[i]]},{i,1,vectors}]];
ecList=Tuples[Table[{randomValues[[5]][[i]],randomValues[[4]][[i]]},{i,1,vectors}]];

ampList={};

Do[
\[Epsilon]=eList[[j]];
\[Epsilon]c=ecList[[j]];
listReplacements=Flatten[{
Table[Spinor[Momentum[Symbol["P"<>ToString[i]]],0,1]->randomValues[[2]][[i]],{i,1,fermions}],
Table[Spinor[-Momentum[Symbol["P"<>ToString[i]]],0,1]->randomValues[[3]][[i]],{i,1,fermions}],
Table[Momentum[Polarization[Symbol["P"<>ToString[fermions+i]],I]]->\[Epsilon][[i]],{i,1,vectors}],
Table[Momentum[Polarization[Symbol["P"<>ToString[fermions+i]],-I]]->\[Epsilon]c[[i]],{i,1,vectors}],
Table[Momentum[Symbol["P"<>ToString[i]]]->randomValues[[1]][[i]],{i,1,scalars+fermions+vectors}]
}];
(*doSlash[]:=IdentityMatrix[4];
doSlash[x_ ,y___]:=slashed[x].doSlash[y];

ampmodIR=ampIR//.WeylChain[s1_,projector_,p___,s2_]->s1 .Projector[projector].f[p]. s2/.f->doSlash;*)

ampmod=amp//.ProjectorSust//.DiracGamma[Momentum[x_]]:>  slashed[Momentum[x]];
ampmod=ampmod//.listReplacements;

ampmod=ampmod//.{Pair[x_List,y_List]->MDot[x,y]}//.slashed->pslash;

AppendTo[ampList,ampmod//.{Eps[x_List,y_List,t_List,w_List]->EpsEval[x,y,t,w]}],
{j,1,Length[eList]}];
Return[ampList];
];


SustMomentaOptimized[amp_List,fermions_,vectors_,scalars_,mlist_]:=Module[{eList,ecList,ampList,ampmodIR,ampmodUV,randomValues,\[Epsilon],\[Epsilon]c},
	randomValues=Rules[mlist,fermions,vectors,scalars];
	eList=Tuples[Table[{randomValues[[4]][[i]],randomValues[[5]][[i]]},{i,1,vectors}]];
	ecList=Tuples[Table[{randomValues[[5]][[i]],randomValues[[4]][[i]]},{i,1,vectors}]];
	
	ampList={};
	
	replaceFunction = MapIndexed[Function[{a,b},a->Slot[b[[1]]]], Flatten[{
				Table[Spinor[Momentum[Symbol["P"<>ToString[i]]],0,1],{i,1,fermions}],
				Table[Spinor[-Momentum[Symbol["P"<>ToString[i]]],0,1],{i,1,fermions}],
				Table[Momentum[Polarization[Symbol["P"<>ToString[fermions+i]],I]],{i,1,vectors}],
				Table[Momentum[Polarization[Symbol["P"<>ToString[fermions+i]],-I]],{i,1,vectors}],
				Table[Momentum[Symbol["P"<>ToString[i]]],{i,1,scalars+fermions+vectors}]
				}]
			];
	
	optimizeAmps = Map[Function@@
		(Experimental`OptimizeExpression[#]//.ProjectorSust//.{Pair->Simplify@*MDot, DiracGamma->pslash, Eps->EpsEval}) /. replaceFunction &,
		amp];
	
	Do[
	\[Epsilon]=eList[[j]];
	\[Epsilon]c=ecList[[j]];
	listReplacements=Flatten[{
	Table[Spinor[Momentum[Symbol["P"<>ToString[i]]],0,1]->randomValues[[2]][[i]],{i,1,fermions}],
	Table[Spinor[-Momentum[Symbol["P"<>ToString[i]]],0,1]->randomValues[[3]][[i]],{i,1,fermions}],
	Table[Momentum[Polarization[Symbol["P"<>ToString[fermions+i]],I]]->\[Epsilon][[i]],{i,1,vectors}],
	Table[Momentum[Polarization[Symbol["P"<>ToString[fermions+i]],-I]]->\[Epsilon]c[[i]],{i,1,vectors}],
	Table[Momentum[Symbol["P"<>ToString[i]]]->randomValues[[1]][[i]],{i,1,scalars+fermions+vectors}]
	}];
	
	(*replaceFunction = MapIndexed[Function[{a,b},a->Slot[b[[1]]]], Keys[listReplacements]];*)
		
	(* We also replace listReplacements again in case OptimizeExpression did something strange *)

	AppendTo[ampList, (#@@Values[listReplacements] /. listReplacements) &/@ optimizeAmps],
	
	{j,1,Length[eList]}];
Return[ampList];
]



SustMomentaSemiOptimized[amp_List,fermions_,vectors_,scalars_,mlist_]:=Module[{eps4,changeparity,
		\[Sigma]s,sigmamuup,sigmabarmuup,gammas,gamm5,gamma5,ProjectorSust,pslash,MDot,EpsEval,eList,ecList,ampList,ampmodIR,ampmodUV,randomValues,\[Epsilon],\[Epsilon]c},

eps4= LeviCivitaTensor[4];
changeparity:={{0,0,1,0},{0,0,0,1},{1,0,0,0},{0,1,0,0}};
\[Sigma]s={IdentityMatrix[2],{{0,1},{1,0}},{{0,-I},{I,0}},{{1,0},{0,-1}}};
sigmamuup=Join[{IdentityMatrix[2]},Table[PauliMatrix[i],{i,3}]];
sigmabarmuup=Join[{IdentityMatrix[2]},-Table[PauliMatrix[i],{i,3}]];
gammas=Table[DiagonalMatrix[{0,0,0,0}],{i,4}];

Do[gammas[[i]][[1;;2,3;;4]]=sigmamuup[[i]];gammas[[i]][[3;;4,1;;2]]=sigmabarmuup[[i]],{i,4}];
gamma5=DiagonalMatrix[{-1,-1,1,1}];
pslash[pmu_List]:=pmu[[1]]gammas[[1]]-Sum[pmu[[i]]gammas[[i]],{i,2,4}];
pslash[0]:=gammas[[1]];
pslash[i_Integer]:=I gammas[[i+1]]/;MemberQ[Range[1,3],i];
MDot[a_List,b_List] := a[[1]]b[[1]]-a[[2;;-1]] . b[[2;;-1]];
EpsEval[x_List,y_List,t_List,w_List]:=-Sum[eps4[[\[Mu],\[Nu],\[Rho],\[Sigma]]]x[[\[Mu]]]y[[\[Nu]]]t[[\[Rho]]]w[[\[Sigma]]],{\[Mu],1,4},{\[Nu],1,4},{\[Rho],1,4},{\[Sigma],1,4}];
EpsEval[x___,y_Integer,z___]:=EpsEval[x,IdentityMatrix[4][[y+1]],z];
ProjectorSust:={DiracGamma[6]->(IdentityMatrix[4]+gamma5)/2,DiracGamma[7]->(IdentityMatrix[4]-gamma5)/2};


	randomValues=Rules[mlist,fermions,vectors,scalars];
	eList=Tuples[Table[{randomValues[[4]][[i]],randomValues[[5]][[i]]},{i,1,vectors}]];
	ecList=Tuples[Table[{randomValues[[5]][[i]],randomValues[[4]][[i]]},{i,1,vectors}]];
	
	ampList={};
	
	replaceFunction = MapIndexed[Function[{a,b},a->Slot[b[[1]]]], Flatten[{
				Table[Spinor[Momentum[Symbol["P"<>ToString[i]]],_,1],{i,1,fermions}],
				Table[Spinor[-Momentum[Symbol["P"<>ToString[i]]],_,1],{i,1,fermions}],
				Table[Momentum[Polarization[Symbol["P"<>ToString[fermions+i]],I]],{i,1,vectors}],
				Table[Momentum[Polarization[Symbol["P"<>ToString[fermions+i]],-I]],{i,1,vectors}],
				Table[Momentum[Symbol["P"<>ToString[i]]],{i,1,scalars+fermions+vectors}]
				}]
			];
	
	optimizeAmps = Map[(Function@@{#}//.ProjectorSust//.{Pair->Simplify@*MDot, DiracGamma->pslash, Eps->EpsEval}) /. replaceFunction &,
		amp];
	
	Do[
	\[Epsilon]=eList[[j]];
	\[Epsilon]c=ecList[[j]];
	listReplacements=Flatten[{
	Table[Spinor[Momentum[Symbol["P"<>ToString[i]]],_,1]->randomValues[[2]][[i]],{i,1,fermions}],
	Table[Spinor[-Momentum[Symbol["P"<>ToString[i]]],_,1]->randomValues[[3]][[i]],{i,1,fermions}],
	Table[Momentum[Polarization[Symbol["P"<>ToString[fermions+i]],I]]->\[Epsilon][[i]],{i,1,vectors}],
	Table[Momentum[Polarization[Symbol["P"<>ToString[fermions+i]],-I]]->\[Epsilon]c[[i]],{i,1,vectors}],
	Table[Momentum[Symbol["P"<>ToString[i]]]->randomValues[[1]][[i]],{i,1,scalars+fermions+vectors}]
	}];
	
	(*replaceFunction = MapIndexed[Function[{a,b},a->Slot[b[[1]]]], Keys[listReplacements]];*)
		
	(* We also replace listReplacements again in case OptimizeExpression did something strange *)
	
	value = (#@@Values[listReplacements] /. listReplacements) &/@ optimizeAmps;
	
	
	value = Expand[value,_LorentzIndex]/. {EpsEval[x___,LorentzIndex[\[Mu]_],y___](a___ . pslash[LorentzIndex[\[Mu]_]] . b___):>a . EpsEval[x,gammas,y] . b};
	
	(*value=Table[Block[{lorIndices},
  
    lorIndices=Echo@DeleteDuplicates[Cases[val,_LorentzIndex,All]];
    
    If[lorIndices=!={}
      ,
      Sum[val,##]&@@(Join[{#,0,3}]&/@lorIndices)
      ,
      val
    ]]
    ,{val,value}];*)
    
	value2={};
	Do[Block[{valList,expandedGammas},
		        valList=Flatten[{PlusToList@val}];
                expandedGammas={};
				Do[Block[{lorIndices},
		              lorIndices=DeleteDuplicates[Cases[sum,_LorentzIndex,All]];
		              If[lorIndices=!={}, AppendTo[expandedGammas,Sum[sum,##]&@@(Join[{#,0,3}]&/@lorIndices)], AppendTo[expandedGammas,sum]];
		             ]; ,{sum,valList}];
		        AppendTo[value2,Total[expandedGammas]]; ]
         ,{val,value}];
	AppendTo[ampList, value2],

	{j,1,Length[eList]}];
Return[ampList];
]


PlusToList[x_Plus]:=List@@x;
PlusToList[x_]:={x};

IndexVariable[a_,indexList_List]:=Symbol[ToString[a]<>ToString[#]]&/@indexList;


Options[ReplaceKinematics]:={
	Momenta->{},
	PolarizationInfo->False};

ReplaceKinematics[amp_,nF_,nV_,nS_,masses_,opt:OptionsPattern[]]:=Flatten@ReplaceKinematics[{amp},nF,nV,nS,masses,opt];

ReplaceKinematics[amp_List,fermions_,vectors_,scalars_,mlist_,OptionsPattern[]]:=Module[{eps4,changeparity,
		\[Sigma]s,sigmamuup,sigmabarmuup,gammas,gamm5,gamma5,ProjectorSust,pslash,MDot,EpsEval,eList,ecList,ampList,ampmodIR,ampmodUV,kins,\[Epsilon],\[Epsilon]c},

	eps4= LeviCivitaTensor[4];
	changeparity:={{0,0,1,0},{0,0,0,1},{1,0,0,0},{0,1,0,0}};
	\[Sigma]s={IdentityMatrix[2],{{0,1},{1,0}},{{0,-I},{I,0}},{{1,0},{0,-1}}};
	sigmamuup=Join[{IdentityMatrix[2]},Table[PauliMatrix[i],{i,3}]];
	sigmabarmuup=Join[{IdentityMatrix[2]},-Table[PauliMatrix[i],{i,3}]];
	gammas=Table[DiagonalMatrix[{0,0,0,0}],{i,4}];
	
	Do[gammas[[i]][[1;;2,3;;4]]=sigmamuup[[i]];gammas[[i]][[3;;4,1;;2]]=sigmabarmuup[[i]],{i,4}];
	gamma5=DiagonalMatrix[{-1,-1,1,1}];
	pslash[pmu_List]:=pmu[[1]]gammas[[1]]-Sum[pmu[[i]]gammas[[i]],{i,2,4}];
	pslash[0]:=gammas[[1]];
	pslash[i_Integer]:=I gammas[[i+1]]/;MemberQ[Range[1,3],i];
	MDot[a_List,b_List] := a[[1]]b[[1]]-a[[2;;-1]] . b[[2;;-1]];
	EpsEval[x_List,y_List,t_List,w_List]:=-Sum[eps4[[\[Mu],\[Nu],\[Rho],\[Sigma]]]x[[\[Mu]]]y[[\[Nu]]]t[[\[Rho]]]w[[\[Sigma]]],{\[Mu],1,4},{\[Nu],1,4},{\[Rho],1,4},{\[Sigma],1,4}];
	EpsEval[x___,y_Integer,z___]:=EpsEval[x,IdentityMatrix[4][[y+1]],z];
	ProjectorSust:={DiracGamma[6]->(IdentityMatrix[4]+gamma5)/2,DiracGamma[7]->(IdentityMatrix[4]-gamma5)/2};


	kins=KinematicConfigurations[fermions,vectors,scalars,mlist];
	eList=Tuples[Table[{kins["e+"][[i]],kins["e-"][[i]]},{i,1,vectors}]];
	ecList=Tuples[Table[{kins["e-"][[i]],kins["e+"][[i]]},{i,1,vectors}]];
	
	ampList={};
	
	replaceFunction = MapIndexed[Function[{a,b},a->Slot[b[[1]]]], Flatten[{
				Table[Spinor[Momentum[Symbol["P"<>ToString[i]]],_,1],{i,1,fermions}],
				Table[Spinor[-Momentum[Symbol["P"<>ToString[i]]],_,1],{i,1,fermions}],
				Table[Momentum[Polarization[Symbol["P"<>ToString[fermions+i]],I]],{i,1,vectors}],
				Table[Momentum[Polarization[Symbol["P"<>ToString[fermions+i]],-I]],{i,1,vectors}],
				Table[Momentum[Symbol["P"<>ToString[i]]],{i,1,scalars+fermions+vectors}]
				}]
			];
	
	momentumChange = If[OptionValue[Momenta]=!={},Thread[OptionValue[Momenta]->Table[Symbol["P"<>ToString[i]],{i,1,scalars+fermions+vectors}]],{}];
	
	optimizeAmps = Map[(Function@@{#}//.ProjectorSust//.{Pair->Simplify@*MDot, DiracGamma->pslash, Eps->EpsEval}) /. replaceFunction &,
		DiracGammaExpand@*ExpandScalarProduct@*Contract@amp /. momentumChange];
	
	Do[
	\[Epsilon]=eList[[j]];
	\[Epsilon]c=ecList[[j]];
	listReplacements=Flatten[{
	Table[Spinor[Momentum[Symbol["P"<>ToString[i]]],_,1]->kins["u"][[i]],{i,1,fermions}],
	Table[Spinor[-Momentum[Symbol["P"<>ToString[i]]],_,1]->kins["vbar"][[i]],{i,1,fermions}],
	Table[Momentum[Polarization[Symbol["P"<>ToString[fermions+i]],I]]->\[Epsilon][[i]],{i,1,vectors}],
	Table[Momentum[Polarization[Symbol["P"<>ToString[fermions+i]],-I]]->\[Epsilon]c[[i]],{i,1,vectors}],
	Table[Momentum[Symbol["P"<>ToString[i]]]->kins["p"][[i]],{i,1,scalars+fermions+vectors}]
	}];
	
	(*replaceFunction = MapIndexed[Function[{a,b},a->Slot[b[[1]]]], Keys[listReplacements]];*)
		
	(* We also replace listReplacements again in case OptimizeExpression did something strange *)
	
	value = (#@@Values[listReplacements] /. listReplacements) &/@ optimizeAmps;
	
	
	value = Expand[value,_LorentzIndex]/. {EpsEval[x___,LorentzIndex[\[Mu]_],y___](a___ . pslash[LorentzIndex[\[Mu]_]] . b___):>a . EpsEval[x,gammas,y] . b};
	
	(*value=Table[Block[{lorIndices},
  
    lorIndices=Echo@DeleteDuplicates[Cases[val,_LorentzIndex,All]];
    
    If[lorIndices=!={}
      ,
      Sum[val,##]&@@(Join[{#,0,3}]&/@lorIndices)
      ,
      val
    ]]
    ,{val,value}];*)
    
	value2={};
	Do[Block[{valList,expandedGammas},
		        valList=Flatten[{PlusToList@val}];
                expandedGammas={};
				Do[Block[{lorIndices},
		              lorIndices=DeleteDuplicates[Cases[sum,_LorentzIndex,All]];
		              If[lorIndices=!={}, AppendTo[expandedGammas,Sum[sum,##]&@@(Join[{#,0,3}]&/@lorIndices)], AppendTo[expandedGammas,sum]];
		             ]; ,{sum,valList}];
		        AppendTo[value2,Total[expandedGammas]]; ]
         ,{val,value}];
	AppendTo[ampList, value2],

	{j,1,Length[eList]}];
	
If[OptionValue[PolarizationInfo],
	Print["Polarization(s) for "<>StringRiffle[Table[Symbol["P"<>ToString[i]],{i,1,scalars+fermions+vectors}][[fermions+1;;fermions+vectors]],", "]<>" read: {"<>
			StringRiffle[StringJoin/@Tuples[Table[{"+","-"},vectors]], ", "]<>"}"];
	];
Return[ampList];
];


SustMomentaRules[amp_List,fermions_,vectors_,scalars_,randomValues_]:=Module[{eList,ecList,ampList,ampmodIR,ampmodUV,\[Epsilon],\[Epsilon]c},

	eList=Tuples[Table[{randomValues[[4]][[i]],randomValues[[5]][[i]]},{i,1,vectors}]];
	ecList=Tuples[Table[{randomValues[[5]][[i]],randomValues[[4]][[i]]},{i,1,vectors}]];
	
	ampList={};
	
	replaceFunction = MapIndexed[Function[{a,b},a->Slot[b[[1]]]], Flatten[{
				Table[Spinor[Momentum[Symbol["P"<>ToString[i]]],0,1],{i,1,fermions}],
				Table[Spinor[-Momentum[Symbol["P"<>ToString[i]]],0,1],{i,1,fermions}],
				Table[Momentum[Polarization[Symbol["P"<>ToString[fermions+i]],I]],{i,1,vectors}],
				Table[Momentum[Polarization[Symbol["P"<>ToString[fermions+i]],-I]],{i,1,vectors}],
				Table[Momentum[Symbol["P"<>ToString[i]]],{i,1,scalars+fermions+vectors}]
				}]
			];
	
	optimizeAmps = Map[Function@@
		(Experimental`OptimizeExpression[#]//.ProjectorSust//.{Pair->Simplify@*MDot, DiracGamma->pslash, Eps->EpsEval}) /. replaceFunction &,
		amp];
	
	Do[
	\[Epsilon]=eList[[j]];
	\[Epsilon]c=ecList[[j]];
	listReplacements=Flatten[{
	Table[Spinor[Momentum[Symbol["P"<>ToString[i]]],0,1]->randomValues[[2]][[i]],{i,1,fermions}],
	Table[Spinor[-Momentum[Symbol["P"<>ToString[i]]],0,1]->randomValues[[3]][[i]],{i,1,fermions}],
	Table[Momentum[Polarization[Symbol["P"<>ToString[fermions+i]],I]]->\[Epsilon][[i]],{i,1,vectors}],
	Table[Momentum[Polarization[Symbol["P"<>ToString[fermions+i]],-I]]->\[Epsilon]c[[i]],{i,1,vectors}],
	Table[Momentum[Symbol["P"<>ToString[i]]]->randomValues[[1]][[i]],{i,1,scalars+fermions+vectors}]
	}];
	
	(*replaceFunction = MapIndexed[Function[{a,b},a->Slot[b[[1]]]], Keys[listReplacements]];*)
		
	(* We also replace listReplacements again in case OptimizeExpression did something strange *)

	AppendTo[ampList, (#@@Values[listReplacements] /. listReplacements) &/@ optimizeAmps],
	
	{j,1,Length[eList]}];
Return[ampList];
]


End[];


EndPackage[];
