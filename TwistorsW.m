(* ::Package:: *)

Eval::usage = "Evaluate spinor products in terms of spinor components";
MomTwi::usage = "Generates the transformation rules from spinors to momentum twistors";
Rsp2tw::usage = "List of replacements to convert Spinor products to momentum twistors";
Rtw2sp::usage = "List of replacements to convert momentum twistors to Spinor products";
RSpiCom::usage = "List of replacements to convert spinor components to momentum twistors";
sp2tw::usage = "Converts Spinor products to momentum twistors";
tw2sp::usage = "Converts momentum twistors to Spinor products";
SpiCom::usage = "Converts spinor components to momentum twistors";
SpabW::usage = "Writes the for 4-vector \[LeftAngleBracket]a|\[Gamma]|b] in twistor variables";
SpbaW::usage = "Writes the for 4-vector [a|\[Gamma]|b\[RightAngleBracket] in twistor variables";
mom::usage = "Writes the momentum of the particle, pi=\[LeftAngleBracket]i|\[Gamma]|i]/2, in twistor variables";
PolVecP::usage = "Writes the polarisation vector, \!\(\*SubscriptBox[\(\[CurlyEpsilon]\), \(i; q\)]\)=\[LeftAngleBracket]q|\[Gamma]|i]/\[Sqrt]2/\[LeftAngleBracket]q|i\[RightAngleBracket], in twistor variables";
PolVecM::usage = "Writes the polarisation vector, \!\(\*SubscriptBox[\(\[CurlyEpsilon]\), \(i; q\)]\)=-[q|\[Gamma]|i\[RightAngleBracket]/\[Sqrt]2/[q|i], in twistor variables";


Eval[exp_]:=Return[ExpandSToSpinors[exp//SpOpen]/.Spaa[i_,j_]:>-\[Zeta][i]\[Eta][j]+\[Zeta][j]\[Eta][i]/.Spbb[i_,j_]:>\[Zeta]b[i]\[Eta]b[j]-\[Zeta]b[j]\[Eta]b[i]];


MomTwi[N1_]:=Module[
{cond,sys,var,Sol1,will1,will2,will3},

If[N1<4,
ClearAll[Rsp2tw,Rtw2sp];
Print["Imposible representation"];
Abort[];
]

If[N1==4,
cond={
\[Zeta][Sp[1]]->1,
\[Zeta][Sp[2]]->0,
\[Zeta][Sp[3]]->1/x[1],
\[Eta][Sp[1]]->0,
\[Eta][Sp[2]]->1,
\[Eta][Sp[3]]->1,
\[Eta][Sp[4]]->1,
\[Zeta]b[Sp[1]]->-1,
\[Zeta]b[Sp[4]]->-1,
\[Eta]b[Sp[2]]->0
};

sys={
Sum[\[Zeta][Sp[i]]\[Zeta]b[Sp[i]],{i,1,N1}]== 0,
Sum[\[Zeta][Sp[i]]\[Eta]b[Sp[i]],{i,1,N1}]== 0,
Sum[\[Eta][Sp[i]]\[Zeta]b[Sp[i]],{i,1,N1}]==0,
Sum[\[Eta][Sp[i]]\[Eta]b[Sp[i]],{i,1,N1}]==0,
s[1,2]==x[1],
s[2,3]/s[1,2]==x[2]
};

var   = {\[Zeta][4//Sp],\[Zeta]b[2//Sp],\[Zeta]b[3//Sp],\[Eta]b[1//Sp],\[Eta]b[3//Sp],\[Eta]b[4//Sp]};
Sol1  = Solve[Eval[sys]//.cond//Flatten,var]//Flatten;
Sol1  = {cond,Sol1}//Flatten//FullSimplify;
will1 = Table[{Spaa[i,j],Spbb[i,j]},{i,1,N1},{j,i+1,N1}]//Flatten;
will2 = Eval[will1]/.Sol1//Factor;
will3 = Table[will1[[i]]->will2[[i]],{i,1,Length[will2]}];
Rsp2tw = will3/.(-a_->b_):>(a->-b);
Rtw2sp =(Table[sys[[i]],{i,5,Length[sys]}]//Solve[#,Table[x[i],{i,1,3N1-10}]]&)[[1]];

];



If[N1>4,

DeclareSpinor@@Table[i,{i,1,N1}];

cond={

\[Zeta][Sp[1]]->1,
\[Zeta][Sp[2]]->0,
Table[\[Zeta][Sp[i]]->Sum[1/Product[x[k],{k,1,j}],{j,1,i-2}],{i,3,N1}],

\[Eta][Sp[1]]->0,
Table[\[Eta][Sp[i]]->1,{i,2,N1}],

\[Zeta]b[Sp[1]]->-1+x[3N1-10]/x[N1-1],
\[Zeta]b[Sp[2]]->-x[1],
\[Zeta]b[Sp[3]]->x[1],

\[Eta]b[Sp[1]]->1,
\[Eta]b[Sp[2]]->0,
\[Eta]b[Sp[3]]->x[1]x[N1-1]
}//Flatten;

sys={
Sum[\[Zeta][Sp[i]]\[Zeta]b[Sp[i]],{i,1,N1}]==0,
Sum[\[Zeta][Sp[i]]\[Eta]b[Sp[i]],{i,1,N1}]==0,
Sum[\[Eta][Sp[i]]\[Zeta]b[Sp[i]],{i,1,N1}]==0,
Sum[\[Eta][Sp[i]]\[Eta]b[Sp[i]],{i,1,N1}]==0,

s[1,2]==x[1],
Table[x[i]==-((Spaa[i,i+1]Spaa[i+2,1])/(Spaa[1,i]Spaa[i+1,i+2])),{i,2,N1-2}],
s[2,3]/s[1,2]==x[N1-1],
Table[x[i]==Sum[Spab[i-N1+5,j,2]/(Spbb[1,2]Spaa[1,i-N1+5]),{j,2,i-N1+4}],{i,N1,2N1-6}],
Table[x[i]==Sum[Spaa[1,Sm[2]+Sm[3],j,i-2N1+10]/(s[2,3]Spaa[1,i-2N1+10]),{j,2,i-2N1+9}],{i,2N1-5,3N1-11}],
s[1,2,3]/s[1,2]==x[3N1-10]
}//Flatten;

var   = Table[{\[Eta]b[Sp[i]],\[Zeta]b[Sp[i]]},{i,4,N1}]//Flatten;
Sol1  = Solve[Eval[sys]//.cond//Flatten,var]//Flatten;
Sol1  = {cond,Sol1}//Flatten//FullSimplify;
will1 = Table[{Spaa[i,j],Spbb[i,j]},{i,1,N1},{j,i+1,N1}]//Flatten;
will2 = Eval[will1]/.Sol1//Factor;
will3 = Table[will1[[i]]->will2[[i]],{i,1,Length[will2]}];
Rsp2tw = will3/.(-a_->b_):>(a->-b);
Rtw2sp =(Table[sys[[i]],{i,5,Length[sys]}]//Solve[#,Table[x[i],{i,1,3N1-10}]]&)[[1]];
];

Print["Momentum twistors for ",N1," particles were generated"];
RSpiCom=Sol1;
]


Unprotect[Sp];
Sp[Sp[a_Integer]]:=Sp[a];
Protect[Sp];


sp2tw[exp_]:=Return[ExpandSToSpinors[exp/.MP[a_?SpinorQ,b_?SpinorQ]:>s[a,b]/2//SpOpen]/.Rsp2tw];
tw2sp[exp_]:=Return[exp/.Rtw2sp];


SpiCom[i_]:={\[Zeta][i//Sp],\[Eta][i//Sp],\[Zeta]b[i//Sp],\[Eta]b[i//Sp]}/.RSpiCom//tw2sp//sp2tw;


GenSpiCom[w2_]:=Module[
{P,p0,p1,p2,p3,lp,lTp},
If[Length[w2]==0,DeclareSpinor[w2]];
P=mom[w2];p0=P[[1]];p1=P[[2]];p2=P[[3]];p3=P[[4]];lp=-I/Sqrt[p0+p3]{p0+p3,p1+I p2}//Factor;
lTp=I/Sqrt[p0+p3]{p0+p3,p1-I p2}//Factor;
SpiCom[w2]={lp,lTp}//Flatten;
];

GenSpiCom[w2_List]:=Module[
{i},
DeclareSpinor@@w2;
For[i=1,i<=Length[w2],i++,
GenSpiCom[w2[[i]]];
];
];


SpaaW[w2_,w3_]:=Module[
{l1,l2},
l1=I PauliMatrix[2].{SpiCom[w2][[1]],SpiCom[w2][[2]]};
l2={SpiCom[w3][[1]],SpiCom[w3][[2]]};
l1.l2//Factor
];
SpbbW[w2_,w3_]:=Module[
{l1,l2},
l1={SpiCom[w2][[3]],SpiCom[w2][[4]]};
l2=I PauliMatrix[2].{SpiCom[w3][[3]],SpiCom[w3][[4]]};
l1.l2//Factor
];
SpabW[{a1_,a2_,s1_,s2_},{b1_,b2_,r1_,r2_}]:={(a1 r1+a2 r2),(a2 r1+a1 r2), I(-a2 r1+a1 r2),(a1 r1-a2 r2)};
SpbaW[a1_List,a2_List]:=SpabW[a2,a1];


mom[i_Plus]:=mom[#]&/@i;
mom[i_]:=SpabW[SpiCom[i],SpiCom[i]]/2;


PolVecP[p1_,r1_]:=SpabW[SpiCom[r1],SpiCom[p1]]/(Sqrt[2]SpaaW[r1,p1])//Factor;
PolVecM[p1_,r1_]:=-SpbaW[SpiCom[r1],SpiCom[p1]]/(Sqrt[2]SpbbW[r1,p1])//Factor;


MPW[i_,j_]:=MP[mom[i],mom[j]]//Factor;
