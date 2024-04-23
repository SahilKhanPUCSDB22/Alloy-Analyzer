open util/ordering[alane]

sig alane
{
l:set lane
}
{
#l=3
}

sig lane
{
has:set people
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
no a:alane|
some a.l&(alane-a).l

no l:lane|
some l.has&(lane-l).has

no p:people|
some p.n&(people-p).n

all p:people,a:alane|a!=last and
p in a.l.has => p.n in a.next.l.has
}

pred p
{
}

run p for exactly 2 alane,exactly 6 lane , exactly 14 people,5 int
