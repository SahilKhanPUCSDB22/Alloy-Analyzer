sig people
{
l:one Int,
seg:one Int,
d:one Int,
st:one Int,
n:disj lone people
}
{
l>0 and l<4
}

abstract sig direction{}
one sig up,down extends direction{}

sig first extends people{}
{}

sig last extends people{}
{
no n
}

let rest = people - last

fact
{
#first=4
//#first<=#last
all f:first|
f.st=1 and no f.~n and f not in (first-f).^n
//all f:first|no f.~n
all p:people|p not in p.^n 
//all disj f1,f2:first|f1 not in f2.n
//all l:last| no l.n
all p:rest|some p.n
all f:first|lone l:last|l in f.^n
all p:rest|p.n.st=p.st.add[1]
all p:rest|p.n.d=p.d
}
/***************************************************
*******************precondition***********************
****************************************************/
fact pre
{
no disj f1,f2:first|f1.seg=f2.seg and f1.l=f2.l
all f:first|f.seg>1 and f.seg<10
all f:first|f.d=0 or f.d=1
}
/**************************************************
********************postcondition*******************
/**************************************************/
fact post
{
all l:last|l.d=0 and l.seg=5 or l.d=1 and l.seg=6
}
/***************************************************
*******************invariant************************/
fact
{
all p:people-last|p.d=0 and 
front[p,p.seg.add[1]] => p.n.seg=p.seg.add[1] and 
p.n.l=p.l

all p:people-last|p.d=1 and 
front[p,p.seg.sub[1]] => p.n.seg=p.seg.sub[1] and 
p.n.l=p.l
}
/***************************************************
*********************predicates*********************/
pred front[p:people,i:Int]
{
no px:people|px.st=p.st and px.seg=i and px.l=p.l
}
pred p{
//all f:first|some l:last|l in f.^n
}
run p for exactly 4 first,exactly 4 last ,
exactly 12 people,9 Int
