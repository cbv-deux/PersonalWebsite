(* ::Package:: *)

Module[{version},version="1.1";
Print[StringJoin["ClusterBruhat_Tools v", version, "."]];
Print["By Quan Hanwen(\:6743 \:701a\:6587)"];
Print["Enter clusterHelp to get help"]]
clusterHelp:=Module[{x},
Print["wordToPermutation[n_list] : Give word in the form of list, compute the corresponding n-permutation."];
Print["GaussianLU[matrix] : Give Gaussian Lower-Diagonal-Upper Matrix decomposition."];
Print["DFVar[\"character: e.g. x\", n] : Give list {x1,...,xn}."];
Print["-----Matrices"];
Print["clusterRealization[n_,list_,vars_] : Generate matrix of word list with fact. vars-vars"];
Print["upMatrix[n_] : Upper n-matrices"];
Print["lowMatrix[n_] : Lower n-matrices"];
Print["wholeMatrix[n_] : Standard n-matrices"];
Print["-----Word operations and rank:"];
Print["representatives[list] : Give each equivalence class a representative"];
Print["reducedWords[p,q] : Given 2 lists of permutation, compute all possible reduced words without circle."];
Print["wordToList : word list to standard forms"];
Print["parseDoubleWord: word/list -> two different words:lists"];
Print["upperRight[lowerLeft]RankMatrix[n,word] : Given word and number n, compute rank conditions in corresponding double Bruhat cell."];
Print["upperRight[lowerLeft]MinorsIndices[n,word] : Minors."];
Print["submatrixRank[matrix, rows, columns,k] : Condition that submatrix of rows and columns have rank k"];
Print["submatrixRank[matrix, word] : Condition that matrix inside a double Bruhat cell"];
Print["-----Computational:"];
Print["myExpandandTogether: \:901a\:5206\:5c55\:5f00\:5316\:7b80"];
Print["Kill[mat,word] : Compute all factorized variables"];
Print["Kill[mat,word] : Compute all combinatoric variables"];
Print["clusterconditionsF[mat,word] : Compute all elements inside factorized variables {a,b} from a/b"];
Print["clusterconditionsC[mat,word] : Compute all elements inside factorized variables {a,b} from a/b"];
Print["compute[mat,perm] : give factorized variables"];
Print["compute[mat,perm] : give combinatorial variables"];
Print["-----Twisted:"];
Print["twisted[mat,word,cword_string/list,list] : compute twisted map for mat and r/c word when elements in list is nonzero.(might have problem!)"];
Print["-----Variety computations:"];
Print["splitEquations[eqns] : Split equation a-b=0 to a=0 or b=0 and give all such or's"];
Print["reduce[expr,condition] : reduce expr when condition holds."];
Print["reduce[expr,mat,word] : reduce expr when mat in word-Bruhat cell."]]

(*Basic functions*)
(* \:51fd\:65701\:ff1a\:5c06\:7b80\:5316\:8bcd word (\:5217\:8868\:ff0c\:6309 s1, s2, ..., sk \:987a\:5e8f) \:8f6c\:6362\:4e3a\:6700\:7ec8\:7f6e\:6362\:5217\:8868 *)
wordToPermutation[n_Integer, word_List] := Module[{perm = Range[n]},
  Do[
    perm = Map[Which[# == s, s + 1, # == s + 1, s, True, #] &, perm],
    {s, word}
  ];
  perm
]

Print["wordToPermutation[n,list]: Give  word in the form of list, compute the corresponding n-permutation."]

SToW[s_String] := ToExpression /@ Characters[s]

(* \:51fd\:65702\:ff1a\:8ba1\:7b97\:65b9\:9635 matrix \:7684\:6307\:5b9a\:884c rows \:548c\:5217 cols \:7684\:5b50\:5f0f\:884c\:5217\:5f0f *)
submatrixDet[matrix_?MatrixQ, rows_List, cols_List] := 
  Det[matrix[[rows, cols]]]

(* \:51fd\:65703\:ff1a\:7ed9\:51fa\:9ad8\:65afLDU\:5206\:89e3 *)
Clear[GaussianLDU];
GaussianLDU[A_?MatrixQ] /; SquareMatrixQ[A] := Module[
  {n, L, U, i, j, k, multiplier, dMat},n = Length[A];
  L = IdentityMatrix[n];
  U = A;
  
  For[k = 1, k < n, k++,
    If[U[[k, k]] == 0,
      Print["Zero pivot at step ", k, " \[Dash] decomposition failed"];
      Return[$Failed];
    ];
    For[i = k + 1, i <= n, i++,
      multiplier = U[[i, k]] / U[[k, k]];
      L[[i, k]] = multiplier;
      U[[i, k]] = 0;
      For[j = k + 1, j <= n, j++,
        U[[i, j]] -= multiplier * U[[k, j]];
      ];
    ];
  ];
  
  dMat = Diagonal[U];
  If[MemberQ[dMat, 0],
    Print["Zero diagonal in U \[Dash] decomposition failed"];
    Return[$Failed];
  ];
  
  {L, DiagonalMatrix[dMat], Transpose[Transpose[U] / dMat]}
]

Print["GaussianLDU[matrix]: Give gaussian Lower-Diagonal-Upper Matrix decomposition."]

DFVar[x_String,n_Integer]:=Table[Symbol[x<>ToString[i]],{i,n}]
Print["DFVar[\"character: eg.x \",n ]: Give list {x1,...,xn}."]

(*matrices and ranks*)
(*Get["E:\\Mathematica\\QSG\\Cluster_real_double_Bruhat.m"]*)
Print["-----Matrices"]
e[k_,m_,n_][t_]:=Table[Boole[x==y]+t Boole[x==k]Boole[y==k+1],{x,m+n},{y,m+n}]
f[k_,m_,n_][t_]:=Table[Boole[x==y]+t Boole[x==k+1]Boole[y==k],{x,m+n},{y,m+n}]
h[k_,m_,n_][t_]:=Table[Boole[x==y]+(t-1)* Boole[x==k]*Boole[y==k],{x,m+n},{y,m+n}]

clusterRealization[n_,list_,vars_]:=Module[{new,var,queue},new=IdentityMatrix[n];  queue=vars;  Do[var=Identity @@ Take[queue,1];queue=Drop[queue,1];
If[Head[i]===OverBar,new=f[Identity @@ i,n,0][var ] . new,If[Head[i]===circle, new=h[Identity @@ i,n,0][var ] . h[(Identity @@ i)+1,n,0][var^(-1)] . new,new=e[i,n,0][var] . new
]],{i,list}];new]
Print["clusterRealization[n_,list_,vars_]: Generate matrix of word list with fact. vars=vars"]
upMatrix[n_]:=Table[Which[i<=j,Symbol["a"<>ToString[i]<>ToString[j]],True,0],{i,n},{j,n}]
lowMatrix[n_]:=Table[Which[i>=j,Symbol["a"<>ToString[i]<>ToString[j]],True,0],{i,n},{j,n}]
wholeMatrix[n_]:=Table[Which[True,Symbol["a"<>ToString[i]<>ToString[j]],True,0],{i,n},{j,n}]
Print["upMatrix[n_]: Upper n-matrices"]
Print["lowMatrix[n_]: Lower n-matrices"]
Print["wholeMatrix[n_]: Standard n-matrices"]
multiplyRight[perm_List,i_Integer]:=ReplacePart[perm,{i->perm[[i+1]],i+1->perm[[i]]}]
isIdentity[perm_List]:=perm==Range[Length[perm]];

(*WORD OPERATIONS*)
Print["-----Word operations and rank:"]


(*\:4ece\:5e26\:6807\:8bb0\:7684\:6570\:4e2d\:63d0\:53d6\:7528\:4e8e\:6bd4\:8f83\:7684\:6570\:503c*)getValue[x_Integer]:=x;
getValue[x_]:=With[{h=Head[x]},If[MatchQ[h,Overbar|Underbar],First[x],(*\:5bf9\:5176\:4ed6\:5e26\:6807\:8bb0\:7684\:6570\:ff0c\:5c1d\:8bd5\:53d6\:7b2c\:4e00\:4e2a\:53c2\:6570*)If[Length[x]>0&&AtomQ[First[x]],First[x],x]]];
(*\:5224\:65ad\:4e24\:4e2a\:76f8\:90bb\:5143\:7d20\:53ef\:5426\:4ea4\:6362*)
canSwap[a_,b_]:=If[Head[a]===Head[b], Abs[getValue[a]-getValue[b]]>1,getValue[a]!=getValue[b]];
(*\:751f\:6210\:4e00\:6b21\:4ea4\:6362\:5f97\:5230\:6240\:6709\:90bb\:5c45*)
neighbors[list_List]:=Module[{n=Length[list],res={}},Do[If[canSwap[list[[i]],list[[i+1]]],AppendTo[res,ReplacePart[list,{i->list[[i+1]],i+1->list[[i]]}]]],{i,1,n-1}];
res];
(*\:751f\:6210\:4e00\:4e2a\:5217\:8868\:7684\:7b49\:4ef7\:7c7b\:ff08\:95ed\:5305\:ff09*)
closure[start_List]:=FixedPoint[Union[#,Catenate[neighbors/@#]]&,{start}];
(*\:4e3b\:51fd\:6570\:ff1a\:4ece\:4e00\:65cf\:5217\:8868\:4e2d\:63d0\:53d6\:7b49\:4ef7\:7c7b\:4ee3\:8868\:5143*)
representatives[lists_List]:=Module[{out={},equivClasses={}},Do[With[{elem=lists[[i]]},If[!MemberQ[Catenate[equivClasses],elem],AppendTo[equivClasses,closure[elem]];
AppendTo[out,elem]]],{i,Length[lists]}];
out]
Print["representatives[list]: Give each equivalence class a representative"]

reducedWords[p_List,q_List]:=reducedWords[p,q]=Module[{n=Length[p],res={},wordList},(*\:82e5\:4e24\:4e2a\:90fd\:662f\:5355\:4f4d\:5143\:ff0c\:8fd4\:56de\:7a7a\:5217\:8868*)If[isIdentity[p]&&isIdentity[q],Return[{{}}]];
(*\:5c1d\:8bd5\:6700\:540e\:4e00\:4e2a\:751f\:6210\:5143\:6765\:81ea\:7b2c\:4e00\:4e2a\:56e0\:5b50*)Do[If[p[[i]]>p[[i+1]],wordList=reducedWords[multiplyRight[p,i],q];
Do[AppendTo[res,Append[word,i]],{word,wordList}]],{i,1,n-1}];
(*\:5c1d\:8bd5\:6700\:540e\:4e00\:4e2a\:751f\:6210\:5143\:6765\:81ea\:7b2c\:4e8c\:4e2a\:56e0\:5b50*)Do[If[q[[i]]>q[[i+1]],wordList=reducedWords[p,multiplyRight[q,i]];
Do[AppendTo[res,Append[word,OverBar[i]]],{word,wordList}]],{i,1,n-1}];
res];
(*\:4e3b\:51fd\:6570\:ff1a\:8f93\:5165\:4e24\:4e2a\:7f6e\:6362\:ff08\:5217\:8868\:5f62\:5f0f\:ff09\:ff0c\:8f93\:51fa\:6240\:6709reduced word*)
generateReducedWords[p_List,q_List]:=reducedWords[p,q];
Print["reducedWords[p,q]\:ff1aGiven 2 lists of permutation, compute all possible reduced words without circle."];

wordToList[s_String]:=Module[{chars=Characters[s],i=1,
n,result={},c,next},While[i<=Length[chars],c=chars[[i]];
If[!MemberQ[CharacterRange["0","9"],c],i++;Continue[]];
n=ToExpression[c];
If[i<Length[chars],next=chars[[i+1]];
Which[next=="'",AppendTo[result,OverBar[n]];i+=2,next=="@",AppendTo[result,circle[n]];i+=2,True,AppendTo[result,n];i+=1],(*\:6700\:540e\:4e00\:4e2a\:5b57\:7b26*)AppendTo[result,n];i+=1];];
result];
Print["wordToList: word to list in standard forms"];

parseDoubleWord[n_Integer, word_]:=Module[{lst,uPerm,vPerm,x},(*\:7edf\:4e00\:4e3a\:5217\:8868\:5f62\:5f0f*)lst=If[StringQ[word],wordToList[word],word];
uPerm=Range[n];
vPerm=Range[n];
Do[Switch[Head[x],Integer,If[1<=x<=n-1,uPerm[[{x,x+1}]]=uPerm[[{x+1,x}]]];,OverBar,x=First[x];(*\:63d0\:53d6 OverBar \:5185\:7684\:6570\:503c*)If[1<=x<=n-1,vPerm[[{x,x+1}]]=vPerm[[{x+1,x}]]];,circle,(*circle \:4e0d\:5f71\:54cd\:7f6e\:6362\:ff0c\:5ffd\:7565*)Null],{x,lst}];
{uPerm,vPerm}];
Print["parseDoubleWord: word/list -> two different words/lists"];

upperRightRankMatrix[n_Integer,word_]:=Module[{lst,uPerm,vPerm,m,k},lst=If[StringQ[word],wordToList[word],word];{uPerm,vPerm}=parseDoubleWord[n,Reverse @ lst];
Table[Count[Take[uPerm,m],x_/;x>=n-k+1],{k,1,n},{m,1,n}]];
lowerLeftRankMatrix[n_Integer,word_]:=Module[{uPerm,vPerm,m,k,lst},lst=If[StringQ[word],wordToList[word],word];{uPerm,vPerm}=parseDoubleWord[n, lst];
Table[Count[Take[vPerm,k],x_/;x>=n-m+1],{k,1,n},{m,1,n}]];
Print["upperRight(lowerLeft)RankMatrix[n,word]: Given word and number n, compute rank conditions in corresponding double Bruhat cell."];

minor[mat_,rows_List,cols_List]:=Simplify @ Det[mat[[rows,cols]]];

(*2. \:751f\:6210\:5de6\:4e0b\:89d2 j \:5b50\:77e9\:9635\:4e2d\:6240\:6709 k\[Times]k \:5b50\:5f0f\:7684\:884c\:5217\:7d22\:5f15\:7ec4\:5408*)
(*n:\:77e9\:9635\:9636\:6570 i:\:5de6\:4e0b\:533a\:57df\:7684\:884c\:6570 (\:884c\:8303\:56f4 n-i+1.. n) j:\:5de6\:4e0b\:533a\:57df\:7684\:5217\:6570 (\:5217\:8303\:56f4 1.. j) k:\:5b50\:5f0f\:5927\:5c0f*)
lowerLeftMinorsIndices[n_Integer,i_Integer,j_Integer,k_Integer]:=Module[{rowSet,colSet,rowCombs,colCombs},rowSet=If[2-i<=0,Range[n-i+2,n],{}];
colSet=Range[1,j];
If[k>i||k>j,Return[{}]];
rowCombs=Flatten[{{n-i+1},#}]& /@ Subsets[rowSet,{k-1}];
colCombs=Subsets[colSet,{k}];
Flatten[Outer[List,rowCombs,colCombs,1],1]];

(*3. \:751f\:6210\:53f3\:4e0a\:89d2 i\[Times]j \:5b50\:77e9\:9635\:4e2d\:6240\:6709 k\[Times]k \:5b50\:5f0f\:7684\:884c\:5217\:7d22\:5f15\:7ec4\:5408*)
(*n:\:77e9\:9635\:9636\:6570 i:\:53f3\:4e0a\:533a\:57df\:7684\:884c\:6570 (\:884c\:8303\:56f4 1.. i) j:\:53f3\:4e0a\:533a\:57df\:7684\:5217\:6570 (\:5217\:8303\:56f4 n-j+1.. n) k:\:5b50\:5f0f\:5927\:5c0f*)
upperRightMinorsIndices[n_Integer,i_Integer,j_Integer,k_Integer]:=Module[{rowSet,colSet,rowCombs,colCombs},rowSet=Range[1,i-1];
colSet=Range[n-j+1,n];
If[k>i||k>j,Return[{}]];
rowCombs=Flatten[{#,{i}}]& /@ Subsets[rowSet,{k-1}];
colCombs=Subsets[colSet,{k}];
Flatten[Outer[List,rowCombs,colCombs,1],1]];
Print["upperRight(lowerLeft)MinorsIndices[n,word]:Minors."];

submatrixRank[matrix_?MatrixQ,rowIndices_List,colIndices_List,k_Integer]:=Module[{submat,nRows,nCols,rowSubsets,colSubsets,kMinors,kPlus1Minors,cond1,cond2},(*1. \:63d0\:53d6\:5b50\:77e9\:9635*)submat=matrix[[rowIndices,colIndices]];
{nRows,nCols}=Dimensions[submat];
(*\:8fb9\:754c\:60c5\:51b5\:ff1ak \:8d85\:51fa\:53ef\:80fd\:8303\:56f4\:5219\:79e9\:4e0d\:53ef\:80fd\:4e3a k*)If[k>Min[nRows,nCols],Return[False]];
(*2. \:79e9\:4e3a 0 \:7684\:7279\:6b8a\:5904\:7406\:ff1a\:6240\:6709\:5143\:7d20\:4e3a\:96f6*)If[k==0,Return[Apply[And,(# == 0)& /@ Flatten[submat]]]];
(*3. \:8ba1\:7b97\:6240\:6709 k\[Times]k \:5b50\:5f0f\:7684\:884c\:5217\:5f0f*)rowSubsets=Subsets[Range[nRows],{k}];
colSubsets=Subsets[Range[nCols],{k}];
kMinors=Table[Det[submat[[r,c]]],{r,rowSubsets},{c,colSubsets}];
(*\:6761\:4ef61\:ff1a\:81f3\:5c11\:6709\:4e00\:4e2a k \:9636\:5b50\:5f0f\:975e\:96f6*)cond1=Apply[Or,(# != 0)& /@ Flatten[kMinors]];
(*4. \:8ba1\:7b97\:6240\:6709 (k+1)\[Times](k+1) \:5b50\:5f0f\:7684\:884c\:5217\:5f0f*)If[k>=Min[nRows,nCols],(*\:4e0d\:5b58\:5728\:66f4\:5927\:7684\:5b50\:5f0f\:ff0c\:6761\:4ef62\:81ea\:52a8\:6210\:7acb*)cond2=True,rowSubsets=Subsets[Range[nRows],{k+1}];
colSubsets=Subsets[Range[nCols],{k+1}];
kPlus1Minors=Table[Det[submat[[r,c]]],{r,rowSubsets},{c,colSubsets}];
(*\:6761\:4ef62\:ff1a\:6240\:6709 (k+1) \:9636\:5b50\:5f0f\:5168\:4e3a\:96f6*)cond2=Apply[And,(# == 0)& /@ Flatten[kPlus1Minors]]];
(*5. \:5c06\:4e24\:4e2a\:6761\:4ef6\:7528 And \:7ec4\:5408\:5e76\:8fd4\:56de*)Return @ And[cond1,cond2]];
submatrixRank[matrix_?MatrixQ,word_]:=Module[{lst,queue,n},lst=If[StringQ[word], wordToList[word],word];
queue=True; n=Length[matrix];Do[queue=queue && submatrixRank[matrix, Range[1,i],Range[n-j+1,n],upperRightRankMatrix[n,lst][[j,i]]],{i,1,n},{j,1,n}
];
Do[queue=queue && submatrixRank[matrix, Range[n-i+1,n],Range[1,j], lowerLeftRankMatrix[n,lst][[j,i]]],{i,1,n},{j,1,n}
];
queue=BooleanMinimize @ Simplify[queue];
queue
];
Print["submatrixRank[matrix, rows, columns,k]: Condition that submatrix of rows and columns have rank k"];
Print["submatrixRank[matrix, word]: Condition that matrix inside a double Bruhat cell"];
(*Computational:*)
Print["-----Computational\:ff1a"];
myExpandAndTogether[expr_]:=Module[{together,num,den,numExp,denExp,numFact,denFact,result},together=Together[expr];
num=Numerator[together];
den=Denominator[together];
numExp=Expand[num];
denExp=Expand[den];
numFact=Factor[numExp];
denFact=Factor[denExp];
result=Cancel[numFact/denFact];
Return[result]; (*\:6216\:8005\:8fd4\:56de result\:ff0c\:540c\:65f6\:4e5f\:53ef\:4ee5\:6253\:5370\:6b65\:9aa4*)]
myExpandAndTogether[x_List]:=myExpandAndTogether /@ x
Print["myExpandAndTogether: \:901a\:5206\:5c55\:5f00\:5316\:7b80"]
myexpandit[expr_Expression]:=Module[{together,num,den,numExp,denExp,numFact,denFact,result},If[Head[expr]===And,Return[ And @@ (myexpandit /@ (List @@ expr))]];If[Head[expr]===Equal, Return[ (myexpandit @ (Subtract @@ expr))==0]];together=Together[expr];
num=Numerator[together];
den=Denominator[together];
numExp=Expand[num];
denExp=Expand[den];
numFact=Factor[numExp];
denFact=Factor[denExp];
result=Cancel[numFact/denFact];
Return[Numerator @ result]; (*\:6216\:8005\:8fd4\:56de result\:ff0c\:540c\:65f6\:4e5f\:53ef\:4ee5\:6253\:5370\:6b65\:9aa4*)]
reduceSimpleMatrixsim[x_,word_]:=Module[{n,lst,nbr,it,k,title,next,rk,ans,nmat},n=Length[x];lst=If[StringQ[word],wordToList[word],word];nmat={};title= First[lst]; next=Drop[lst,1]; it=Identity @@ title; nbr=Head[title];
If[nbr===OverBar,
Do[If[lowerLeftRankMatrix[n,next][[m]][[n-it]]!=lowerLeftRankMatrix[n,lst][[m]][[n-it]],k=m;rk=lowerLeftRankMatrix[n,lst][[m]][[n-it]];Break],{m,1,n}] ;
Do[If[minor[x,list[[1]],list[[2]]]=!=0, ans=minor[x,list[[1]],list[[2]]]/minor[x,Flatten[{{it},{Drop[list[[1]],1]}}],list[[2]]];Break],{list,lowerLeftMinorsIndices[n,n-it,k,rk]}];
nmat=f[it,n,0][-ans] . x;
,
Do[If[upperRightRankMatrix[n,next][[m]][[it]]!=upperRightRankMatrix[n,lst][[m]][[it]],k=m;rk=upperRightRankMatrix[n,lst][[m]][[it]];Break],{m,1,n}];
Do[If[minor[x,list[[1]],list[[2]]]=!=0,ans=minor[x,list[[1]],list[[2]]]/minor[x,Flatten[{Drop[list[[1]],{rk,rk}],{it+1}}],list[[2]]];Break],{list,upperRightMinorsIndices[n,it,k,rk]}];
nmat=e[it,n,0][-ans] . x;
];
ans=myExpandAndTogether[ans];
{{nmat, next}, ans}
]
KILL[mat_,word_]:=Module[{n,work,list,done,go,data,elements},n=Length[mat];list={};list=If[StringQ[word],wordToList[word],word];go=list;work=mat;done={};Print[go];
While[go!={},data=reduceSimpleMatrixsim[work,go];done=Flatten[{done,{data[[2]]}}]; {work,go}=data[[1]]];elements=Table[myExpandAndTogether @ work[[i,i]],{i,1,n}];
done=Flatten[{done,elements}];done];
Print["KILL[mat,word]: Compute all factorized variables"];
getNumeratorDenominatorList[exprList_List]:=Table[{Numerator[expr],Denominator[expr]},{expr,exprList}];
clusterconditionsF[x_,y_]:=DeleteDuplicates[Flatten @ getNumeratorDenominatorList[KILL[x,y]]];
clusterconditionsC[x_,y_]:=DeleteDuplicates[Flatten @ getNumeratorDenominatorList[GIVE[x,y]]];


splitWord[list_List]:={Cases[list,_Integer],(*\:63d0\:53d6\:666e\:901a\:6574\:6570*)Cases[list,OverBar[n_]:>n]               (*\:63d0\:53d6\:4e0a\:5212\:7ebf\:4e2d\:7684\:6570\:5b57*)}
GIVE[matrix_, word_]:=Module[
{n,Perm,current,queuel,queuer,l,Ab},Perm=Reverse @ If[StringQ[word], wordToList[word],word];queuel={}; queuer=Perm; l=Length[Perm];n=Length[matrix];Ab={};current=1;
Do[Ab=(Append[Ab,#]&)  @ submatrixDet[rightWordToPermutation[matrix, splitWord[queuer][[1]] ],Range[1,m,1], Range[1,m,1]], {m,1,n}];
Do[queuel=Flatten[{queuel, First[queuer]}];
current=Identity @@ First[queuer];queuer=Drop[queuer,1];(*Print[current,queuel,queuer];*)
Ab=(Append[Ab,#]&)  @ submatrixDet[leftWordToPermutation[rightWordToPermutation[matrix,splitWord[queuer][[1]]], splitWord[Reverse[queuel]][[2]]], Range[1,current,1],Range[1,current,1]](*;Print[leftWordToPermutation[rightWordToPermutation[matrix, splitWord[queuer][[1]]], splitWord[Reverse[queuel]][[2]]]]*), {t,1,l}];
Ab
]
Print["GIVE[mat,word]: Compute all combinatoric variables"];
Print["clusterconditionsF[mat,word]: Compute all elements inside factorized variables(a,b from a/b)"];
Print["clusterconditionsC[mat,word]: Compute all elements inside factorized variables(a,b from a/b)"];


clusterconditionsC[mat_, word_]:=DeleteDuplicates[Flatten @ getNumeratorDenominatorList[KILL[mat,word]]];
compF[x_]:=Or @@ ((# == 0) & /@ x);computeF[m_,n__]:=And @@ (compF /@ (clusterconditionsF[m,#]& /@ representatives[generateReducedWords[n]]));
compC[x_]:=Or @@ ((#!=0)& /@ x);computeC[m_,n_]:=And @@ (compF /@ (clusterconditionsC[m,#]& /@ representatives[generateReducedWords[n]]));
Print["computeF[mat,perm]: give factorized variables"];
Print["computeC[mat,perm]: give combinatorial variables"];

Print["-----Twisted:"]
rowPerm[x_?MatrixQ, i_]:= Module[{new=x},new[[{i,i+1}]]=new[[{i+1,i}]];new[[{i+1}]]=-new[[i+1]];new]
columnPerm[x_?MatrixQ, i_]:= Module[{new=x},new[[All,{i,i+1}]]=new[[All,{i+1,i}]];new[[All,{i+1}]]=-new[[All,i+1]];new]
rowInvPerm[x_?MatrixQ, i_]:= Module[{new=x},new[[{i+1}]]=-new[[i+1]];new[[{i,i+1}]]=new[[{i+1,i}]];new]
columnInvPerm[x_?MatrixQ, i_]:= Module[{new=x},new[[All,{i+1}]]=-new[[All,i+1]];new[[All,{i,i+1}]]=new[[All,{i+1,i}]];new]
leftWordToPermutation[x_?MatrixQ, list_List]:=Module[{new}, new=x; Do[new= rowPerm[new,i],{i,Reverse[list]}];new]
rightWordToPermutation[x_?MatrixQ, list_List]:=Module[{new}, new=x; Do[new= columnPerm[new,i],{i,list}];new]
leftWordToPermutation[n_, list_List]:=leftWordToPermutation[IdentityMatrix[n],list]
rightWordToPermutation[n_, list_List]:=rightWordToPermutation[IdentityMatrix[n],list]
twisted[x_ , rword_List, cword_List,list_List]:=FullSimplify[Transpose[((#[[2]]^{-1} . #[[3]]&)@ (GaussianLDU[leftWordToPermutation[x,rword]])) . (Inverse[#[[1]]] . #[[2]] . Inverse[#[[3]]])& @ (x) . ((#[[1]] . #[[2]]^{-1}&)@ (GaussianLDU[rightWordToPermutation[x,cword]]))]
,{And @@((#!=0)& /@ list)}];
twisted[x_ , rword_String, cword_String,list_List]:=twisted[x,wordToList[rword],wordToList[cword],list]
Print["twisted[mat,rword,cword_string/list,list]: compute twisted map for mat and r/c word when elements in list is nonzero.(might have problem!)"]
Print["-----Variety computations:"];
orlist[x_]:=If[Head[x]===Or, List @@ x, If[x===False,{},{x}]]
andlist[x_]:=If[Head[x]===And, List @@ x, If[x===True,{},{x}]]
closure[x_]:=Select[#, (Head[#]===Equal&)]& /@ x
orsimp[x_]:=Or @@ (FullSimplify /@ orlist[x])
Clear[EliminateZeroVariables];
EliminateZeroVariables[expr_]:=Module[{eqs,zeroEqs,otherEqs,newZero,vars,changed,result},eqs=List@@expr;
(*\:521d\:59cb\:5206\:79bb\:ff1a\:96f6\:53d8\:91cf\:7b49\:5f0f vs \:5176\:4ed6\:7b49\:5f0f*)zeroEqs=Cases[eqs,(sym_Symbol==0)|(0==sym_Symbol)];
otherEqs=Complement[eqs,zeroEqs];
(*\:8fed\:4ee3\:5316\:7b80*)changed=True;
While[changed,changed=False;
(*\:5f53\:524d\:5df2\:77e5\:7684\:6240\:6709\:96f6\:53d8\:91cf*)vars=Cases[zeroEqs,(sym_Symbol==0)|(0==sym_Symbol):>sym,Infinity]//DeleteDuplicates;
If[vars==={},Break[]];
(*\:5bf9\:5176\:4ed6\:7b49\:5f0f\:8fdb\:884c\:66ff\:6362*)otherEqs=ReplaceAll[otherEqs,Thread[vars->0]];
(*\:68c0\:67e5\:66ff\:6362\:540e\:7684\:7b49\:5f0f\:4e2d\:662f\:5426\:4ea7\:751f\:4e86\:65b0\:7684\:96f6\:53d8\:91cf\:7b49\:5f0f*)newZero=Cases[otherEqs,(sym_Symbol==0)|(0==sym_Symbol)];
If[newZero=!={},(*\:5c06\:65b0\:96f6\:53d8\:91cf\:7b49\:5f0f\:79fb\:51fa otherEqs\:ff0c\:52a0\:5165 zeroEqs*)otherEqs=Complement[otherEqs,newZero];
zeroEqs=Union[zeroEqs,newZero];
changed=True;];];
(*\:5220\:9664 any \:5f62\:5982 0==0 \:7684\:5197\:4f59\:7b49\:5f0f\:ff08\:4f46\:4fdd\:7559 var==0 \:7684\:771f\:5b9e\:7b49\:5f0f\:ff09*)zeroEqs=DeleteCases[zeroEqs,0==0|True];
otherEqs=DeleteCases[otherEqs,0==0|True];
(*\:5408\:5e76\:7ed3\:679c*)result=Join[zeroEqs,otherEqs];
If[result==={},True,Apply[And,result]]];

removeSubsumed[list_List]:=Module[{n,keep,i,j,implies},n=Length[list];
keep=ConstantArray[True,n];
(*\:5224\:65ad a \:662f\:5426\:8574\:542b b*)implies[b_,a_]:=Simplify[Implies[a,b]]===True;
(*\:7b2c\:4e00\:6b65\:ff1a\:5904\:7406\:7b49\:4ef7\:5173\:7cfb\:ff0c\:53ea\:4fdd\:7559\:6bcf\:4e2a\:7b49\:4ef7\:7c7b\:4e2d\:7b2c\:4e00\:4e2a\:51fa\:73b0\:7684*)Do[If[!keep[[i]],Continue[]];
Do[If[i==j||!keep[[j]],Continue[]];
If[implies[list[[i]],list[[j]]]&&implies[list[[j]],list[[i]]],keep[[j]]=False  (*\:7b49\:4ef7\:ff0c\:5220\:9664\:540e\:9762\:7684*)];,{j,i+1,n}];,{i,n}];
(*\:7b2c\:4e8c\:6b65\:ff1a\:5220\:9664\:5355\:5411\:88ab\:8574\:542b\:7684\:9879*)Do[If[!keep[[i]],Continue[]];
Do[If[i==j||!keep[[j]],Continue[]];
If[implies[list[[j]],list[[i]]],keep[[i]]=False;Break[]];,{j,n}];,{i,n}];
Pick[list,keep]]
splitEquations[eqns_]:=Module[{eqnList,groups,combos},(*\:6807\:51c6\:5316\:ff1a\:5982\:679c\:8f93\:5165\:662f\:5b57\:7b26\:4e32\:ff0c\:5148\:89e3\:6790\:ff1b\:5982\:679c\:4e0d\:662f\:ff0c\:5219\:4fdd\:6301\:539f\:6837*)eqnList=If[StringQ[eqns],List@@ToExpression[eqns,InputForm,HoldForm],If[Head[eqns]===And,List@@eqns,{eqns}]];
(*\:5bf9\:6bcf\:4e2a\:7b49\:5f0f\:8fdb\:884c\:5904\:7406\:ff0c\:751f\:6210\:4e00\:7ec4\:56e0\:5b50\:7b49\:5f0f\:ff08\:4f5c\:4e3a\:5217\:8868\:ff09*)groups=Table[Module[{lhs,rhs,expr,factored,factors},lhs=eq[[1]];rhs=eq[[2]];
expr=lhs-rhs;
factored=Factor[expr];
(*\:63d0\:53d6\:56e0\:5b50\:ff1a\:5982\:679c\:7ed3\:679c\:662f\:4e58\:79ef\:4e14\:975e\:6570\:5b57\:56e0\:5b50\:ff0c\:5219\:63d0\:53d6\:ff1b\:5426\:5219\:89c6\:4e3a\:5355\:4e00\:56e0\:5b50*)If[Head[factored]===Times,factors=Select[List@@factored,!NumericQ[#]&],factors=If[NumericQ[factored],{},{factored}]];
(*\:5982\:679c\:56e0\:5b50\:5217\:8868\:4e3a\:7a7a\:ff08\:4f8b\:5982 0==0 \:6216\:5e38\:6570==0\:ff09\:ff0c\:5219\:8df3\:8fc7\:8be5\:7b49\:5f0f*)If[factors==={},{},Map[#==0&,factors]]],{eq,eqnList}];
(*\:79fb\:9664\:7a7a\:7ec4\:ff08\:5982\:679c\:6709\:6052\:7b49\:5f0f\:ff0c\:4e0d\:4ea7\:751f\:7ea6\:675f\:ff09*)groups=Select[groups,#=!={}&];
(*\:5982\:679c\:6ca1\:6709\:6709\:6548\:7ec4\:ff0c\:8fd4\:56de\:7a7a\:5217\:8868\:6216\:4e00\:4e2a\:7a7a And*)If[groups==={},Return[{}]];
(*\:7b1b\:5361\:5c14\:79ef*)combos=Tuples[groups];
(*\:7ec4\:5408\:6210 And \:8868\:8fbe\:5f0f*)Map[And@@#&,combos]];
Print["splitEquations[eqns]: Split equation ab=0 to a=0 or b=0 and give all such or's"]
change[x_]:= Or @@ splitEquations[x];
reduce[x_,condition_:True]:=Or @@ DeleteDuplicates @ Flatten[orlist /@ (BooleanMinimize /@((And @@ Simplify[#,Assumptions-> condition])& /@ ((change/@ # )& /@ (andlist /@(orlist @ BooleanMinimize[Simplify[removeMutualSubsumed [Or @@ EliminateZeroVariables /@ (orlist @ x)], Assumptions->condition]])))))];
(*\:5224\:65ad expr1 \:662f\:5426\:8574\:542b expr2*)impliesQ[expr1_,expr2_]:=FullSimplify[((!(expr2) )&& expr1)===False];
reduce[x_,mat_,word_]:=reduce[x,Simplify @ submatrixRank[mat,word]];
reduce[x_,mat_,word_,n_]:=reduce[reduce[x,submatrixRank[mat,word],n-1],mat,word];
reduce[x_,mat_,word_,1]:=reduce[x,mat,word];
(*\:5224\:65ad expr1 \:662f\:5426\:8574\:542b expr2*)impliesQ[expr1_,expr2_]:=FullSimplify[((!(expr2) )&& expr1)===False];
Print["reduce[expr,condition]: reduce expr when condition holds."];
Print["reduce[expr,mat,word]: reduce expr when mat in word-Bruhat cell."];
(*\:5220\:9664\:6240\:6709\:53c2\:4e0e\:8574\:542b\:5173\:7cfb\:7684\:9879\:ff08\:5373\:5982\:679c\:5b58\:5728 i\[NotEqual]j \:4f7f\:5f97 i\[DoubleRightArrow]j \:6216 j\[DoubleRightArrow]i\:ff0c\:5219 i \:548c j \:90fd\:5220\:9664\:ff09*)
removeMutualSubsumed[expr_]:=Module[{list,n,keep,i,j},If[Head[expr]=!=Or,Return[expr]];
list=List@@expr;
n=Length[list];
keep=ConstantArray[True,n];
(*\:904d\:5386\:6240\:6709\:65e0\:5e8f\:5bf9 (i,j)\:ff0c\:6807\:8bb0\:6709\:8574\:542b\:5173\:7cfb\:7684\:4e24\:9879*)Do[If[i==j,Continue[]];
If[impliesQ[list[[i]],list[[j]]],keep[[i]]=False],{i,n},{j,i+1,n}];
(*\:4fdd\:7559\:672a\:88ab\:6807\:8bb0\:7684\:9879*)With[{result=Pick[list,keep]},If[result==={},False,If[Length[result]==1,First[result],Or@@result]]]];

clusterconditionsC[matrix_, word_]:=Module[
{current,queue,l,Ab,n}, queue=word; l=Length[word];Ab={};current=1;n=Length[matrix];
Do[Ab=(Append[Ab,#]&)  @ submatrixDet[matrix ,(#)&  /@ Range[1,m,1],(wordToPermutation[n, Reverse[queue]][[#]]&) /@ Range[1,m,1]], {m,1,n}];
Do[current=ToExpression[StringTake[queue,1]];queue=StringDrop[queue,1];Ab=(Append[Ab,#]&)  @ submatrixDet[matrix,(#)&  /@ Range[1,current,1],(wordToPermutation[n, SToW[StringReverse[ queue]]][[#]]&) /@ Range[1,current,1]], {t,1,l-1}];

Ab
]




