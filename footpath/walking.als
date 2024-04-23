open util/ordering[lane]

sig lane
{
lane1:set people,
lane2:set people,
lane3:set people
}

sig people
{
seg:one Int,
dest:one end,
n:lone people
}

abstract sig end{}
one sig end1,end2 extends end{}

fact
{
all p:people,l:lane|l!=last and p in l.(lane1+lane2+lane3) =>
p.n.dest=p.dest

//all l:lane|l=first =>
//#l.(lane1+lane2+lane3)=2

all p:people,l:lane|l!=last and 
p.seg<=5 and p.seg>=1 and p in l.(lane1+lane2+lane3) => some p.n

all p:people,l:lane|l!=last and p in l.(lane1+lane2+lane3) =>
p not in l.^next.(lane1+lane2+lane3)

all p:people,l:lane|//l!=last and
p in l.(lane1+lane2+lane3) => p.seg>=1 and p.seg<=5

all p:people,l:lane|l!=last and p in l.(lane1+lane2+lane3) =>
p.n in l.next.(lane1+lane2+lane3)

no l:lane|
some l.lane1&l.lane2

no l:lane|
some l.lane2&l.lane3 

no l:lane|
some l.lane1&l.lane3 

no l:lane,p:people|
p in l.lane1 and
some p.seg&(l.lane1-p).seg

no l:lane,p:people|
p in l.lane2 and
some p.seg&(l.lane2-p).seg

no l:lane,p:people|
p in l.lane3 and
some p.seg&(l.lane3-p).seg

no p1,p2:people|p1!=p2 and
some p1.n&p2.n

all l:lane|l=first =>
some x,y:people|x!=y and x.dest=end1 and y.dest=end2 and 
x+y in l.(lane1+lane2+lane3)

all p:people|p in first.(lane1+lane2+lane3) and p.dest=end1 => p.seg>1 

all p:people|p in first.(lane1+lane2+lane3) and p.dest=end2 => p.seg<7

all p:people,l:lane|l!=last and p in l.(lane1+lane2+lane3) and
p.dest=end1 => p.n.seg=p.seg or  p.n.seg=p.seg.sub[1]  

all p:people,l:lane|l!=last and p in l.(lane1+lane2+lane3) and
p.dest=end2 => p.n.seg=p.seg or  p.n.seg=p.seg.add[1]
}

pred p
{
some x,y:people|y in first.(lane1+lane2+lane3) and 
y.seg=1 and 
x in last.(lane1+lane2+lane3) and x.seg=5 and 
x.dest=end2 and
x in y.^n
}

pred x
{
one x,y:people|y in first.(lane1+lane2+lane3) and 
y.seg=1 and 
x in last.(lane1+lane2+lane3) and x.seg=5 and 
x.dest=end2 and
x in y.^n

one x,y:people|y in first.(lane1+lane2+lane3) and 
y.seg=5 and 
x in last.(lane1+lane2+lane3) and x.seg=1 and 
x.dest=end1 and
x in y.^n
}

pred n
{
some x,y:people,l:lane|l!=last and l!=first and
y in l.(lane1+lane2+lane3) and 
no y.~n and 
x in last.(lane1+lane2+lane3) and x.seg=5 and 
x.dest=end2 and
x in y.^n
}
run n for exactly 5 lane, exactly 13 people,5 int
run p for exactly 5 lane, exactly 10 people,5 int
run x for exactly 5 lane, exactly 10 people,5 int
