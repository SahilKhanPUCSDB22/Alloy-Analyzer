open util/ordering[path]

/*********************************************************/
sig path{
has : disj set lane
}
{
#has=3
}

sig lane
{
contains :disj set people,
nxl:disj lone lane
}

sig people
{
seg : one Int,
nxt : disj lone people,
end : one dest
}

abstract sig dest{}
one sig end1,end2 extends dest{}

pred p{}
run p for exactly 4 path , 12 lane , 16 people, 5 Int
/*********************Rules***********************************/
fact
{
//everythiing on path
all p:people|p in lane.contains

//no cycle
no p:people|p in p.^nxt
no l:lane|l in l.^nxl

//first will not be in someone's nxt
all p:people|p in first.has.contains => no p.~nxt

//everything not in last will have some nxt
all p:people|p not in last.has.contains <=>some p.nxt
all l:lane|l not in last.has <=> some l.nxl

//cant come directly in last
all p:people|p in last.has.contains => some p.~nxt 

//next in next state
all p:people,pa:path|p in pa.has.contains and some p.nxt=>
p.nxt in pa.next.has.contains
all l:lane,pa:path|l in pa.has and some l.nxl =>
l.nxl in pa.next.has 

//end remains same
all p:people|some p.nxt => p.nxt.end=p.end
}
/*************************Preconditions******************************/
fact precondition
{
#first.has.contains=4

//segno
all p:people|p in first.has.contains =>
p.seg<=5 and p.seg>=3

//no one on the same seg in first state
no disj p1,p2:people,l:lane|p1+p2 in l.contains and 
l in first.has and 
some p1.seg&p2.seg

//one who comes in between must not violate rules
all p:people,pa:path,l:lane|p in l.contains and
l in pa.has and pa!=first and no p.~nxt => 
p.seg!=(l.contains-p).seg and p.seg >=2 and p.seg <=6
}
/***********************Checking********************************/
check
{
no disj p1,p2:people,l:lane,pa:path|
l in pa.has and p1+p2 in l.contains and p1.seg=p2.seg
}
for 6 path , 18 lane , 30 people ,7 Int

/*****************Initiate predicates*****************************/
fact
{
all p:people,l:lane,pa:path|pa!=last and l in pa.has 
and p in l.contains and p.end=end2 => moveend2[p,l,pa]

all p:people,l:lane,pa:path|pa!=last and l in pa.has 
and p in l.contains and p.end=end1 => moveend1[p,l,pa]
}
/******************possible transitions***************************/
//predicate for people going to end1
pred moveend2[p:people,l:lane,pa:path]
{
//front seg empty
no p.seg.add[1] & (l.contains-p).seg => 
ns[p,l,p.seg.add[1]] 

//front seg occupied
some p.seg.add[1] & (l.contains-p).seg =>
goside[p,(pa.has-l),p.seg.add[1]]

//all l:pa.has | some p.seg.add[1] & l.contains.seg => wait [p,l]
}

//predicate for people going to end1
pred moveend1[p:people,l:lane,pa:path]
{
//front seg empty
no p.seg.sub[1] & (l.contains-p).seg => 
ns[p,l,p.seg.sub[1]]

//front seg occupied
some p.seg.sub[1] & (l.contains-p).seg =>
goside[p,(pa.has-l),p.seg.sub[1]]

//all l:pa.has | some p.seg.sub[1] & l.contains.seg => wait [p,l] 
}
/*********************preds*************************************/
//predicate for waiting
pred wait[p:people,l:lane]
{
p.nxt.seg=p.seg and p.nxt in l.nxl.contains
}

//predicate for correct transition
pred ns[p:people,l:lane,i:Int]
{
p.nxt.seg=i and p.nxt in l.nxl.contains
}

//predicate for going into side lane
pred goside[p:people,l:lane,i:Int]
{
some lx:l|no i&(lx.contains.seg) => ns[p,lx,i]
all lx:l|some i&(lx.contains.seg) => wait[p,p.~contains]
}
/*******************************************************************/
