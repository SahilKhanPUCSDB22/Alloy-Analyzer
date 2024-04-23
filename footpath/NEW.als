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
contains :disj set people
}

sig people
{
seg : one Int,
nxt : disj lone people,
end : one dest
}

abstract sig dest{}
one sig end1,end2 extends dest{}
/********************************************************/
fact
{
#first.has.contains>0

//dest remains same
all p:people|some p.nxt => p.nxt.end=p.end

//no cycle
no p:people|p in p.^nxt

//people next in next
all p:people,pa:path|p in pa.has.contains and pa!=last =>
p.nxt in pa.next.has.contains

//no one directly in last
all p:people|p in last.has.contains => some p.~nxt

//no people with invalid seg no in between
all p:people| no p.~nxt => p.seg >1 and p.seg <7 

all p:people,pa:path|pa!=last and 
p in pa.has.contains => some p.nxt

all p:people| p in first.has.contains =>
p.seg=1 and p.end=end2 or
p.seg=7 and p.end=end1
}


pred p{}
run p for exactly 4 path ,12  lane , 8 people , 5 Int

fact move
{
//fixed final states
all p:people,pa:path|pa!=last and p in pa.has.contains and
p.seg=1 or p.seg=7  => p.nxt.seg=p.seg

all p:people,pa:path|pa!=last and p in pa.has.contains and
p.seg>1 and p.end=end1 => down[pa,p] 

all p:people,pa:path|pa!=last and p in pa.has.contains and
p.seg<7 and p.end=end2 => up[pa,p]

//all p:people,pa:path|pa!=last and p in pa.has.contains and 
//p.end=end2 =>
//p.nxt.seg=p.seg.add[1] 
//
//all p:people,pa:path|pa!=last and p in pa.has.contains and 
//p.end=end1 =>
//p.nxt.seg=p.seg.sub[1]
}

pred up[pa:path,p:people]
{
all l:pa.has|all px:people|px+p in l.contains and 
px!=p and px.seg!=p.seg.add[1] =>
p.nxt in l.contains and p.nxt.seg=p.seg.add[1] 
}

pred down[pa:path,p:people]
{
all l:pa.has|all px:people|px+p in l.contains and 
px!=p and px.seg!=p.seg.sub[1] =>
p.nxt in l.contains and p.nxt.seg=p.seg.sub[1]
}
