sig people
{
l:one Int,
seg:one Int,
d:one direction,
st:one Int,
n:disj lone people
}
{
l>0 and l<4
}

one sig lanes
{
number:set Int
}
{
number=1+2+3
}

abstract sig direction{}
one sig inc,dec extends direction{}

sig first in people{}
{}

sig last in people{}
{
no n
}

let rest = people - last 

fact
{
#first=4
#last=4
all f:first|
f.st=-16 and no f.~n and f not in (first-f).^n
all p:people|p not in p.^n 
all p:rest|p.n.d=p.d and p.n.st=p.st.add[1]
//all f:first|lone l:last|l in f.^n
//some f:first | f.d!=(first-f).d
//no f:first|f.l=3
}

check
{
no disj p1,p2:people|
p1.st=p2.st and p1.l=p2.l and p1.seg=p2.seg
} for 20 people , 5 int

check
{
no p:rest|move[p,p.seg.add[1],p.l] => p.l!=p.n.l and p.n.seg <= p.seg
}for 10 people , 5 int
/*****************precondition***********************/

fact pre
{
//no rule violation at the start
no disj f1,f2:first|f1.seg=f2.seg and f1.l=f2.l

//all elements at start are between 1-10
all f:first | f.d=inc => f.seg >-1 and f.seg<5
all f:first | f.d=dec => f.seg >0 and f.seg<6

//all elements will have fixed direction
all f:first|f.d=dec or f.d=inc
}

/******************invariant************************/

/*******************inc***************************/

fact
{
all p:rest|p.d=inc and 
laneempty[p,p.seg.add[1],p.seg.add[2],p.l] => move[p,p.seg.add[1],p.l]

all p:rest|p.d=inc and
lanefull[p,p.seg.add[1],p.seg.add[2],p.l] => some lx:(lanes.number-p.l)|
laneempty[p,p.seg.add[1],p.seg.add[2],lx] => move[p,p.seg.add[1],lx] 

all p:rest|p.d=inc and
lanefull[p,p.seg.add[1],p.seg.add[2],p.l] => all lx:(lanes.number-p.l)|
lanefull[p,p.seg.add[1],p.seg.add[2],lx] => nomove[p,p.seg]   
/********************dec***************************/
all p:rest|p.d=dec and
laneempty[p,p.seg.sub[1],p.seg.sub[2],p.l] => move[p,p.seg.sub[1],p.l] 

all p:rest|p.d=dec and
lanefull[p,p.seg.sub[1],p.seg.sub[2],p.l] => some lx:(lanes.number-p.l)|
laneempty[p,p.seg.sub[1],p.seg.sub[2],lx] => move[p,p.seg.sub[1],lx]

all p:rest|p.d=dec and
lanefull[p,p.seg.sub[1],p.seg.sub[2],p.l] => all lx:(lanes.number-p.l)|
lanefull[p,p.seg.sub[1],p.seg.sub[2],lx] => nomove[p,p.seg]
}

/*********************predicates*********************/

//checks segment
pred segcheck[p:people,i,j:Int]
{
p.seg=i or p.seg=j
}

//makes move
pred move[p:people,i,lx:Int]
{
p.n.seg=i and p.n.l=lx
}

//makes no move
pred nomove[p:people,i:Int]
{
p.n.seg=i and p.n.l=p.l
}

//checks lane
pred laneempty[p:people,i,j,lx:Int]
{
no px1:people|p!=px1 and
px1.st=p.st and px1.seg=i and px1.l=lx or
px1.st=p.st and px1.seg=j and px1.l=lx
}

//checks lane empty
pred lanefull[p:people,i,j,lx:Int]
{
some px1:people|p!=px1 and
px1.st=p.st and px1.seg=i and px1.l=lx or
px1.st=p.st and px1.seg=j and px1.l=lx
}

/*******************running*************************/

pred p
{
//#people>7
}
run p for exactly 8 people,5 int

/********************postcondition*******************/
fact post
{
//all l:people|l.d=inc and l.seg=6 <=> l in last 
all l:people|l.d=dec and l.seg=0 or l.d=inc and l.seg=5 <=> l in last
//all l:last|l.d=dec => l.seg=5
}
