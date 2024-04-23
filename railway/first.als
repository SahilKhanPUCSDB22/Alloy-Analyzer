abstract sig track
{
num:one Int,
side:lone strack,
utrack:lone track,
dtrack:lone track,
has :lone train
}

one sig strack{}

abstract sig train{}

one sig t1,t2 extends train{}

fact
{
one t:track|(track-t) in t.^dtrack and no t.utrack
and t.num=1

no t:track|t in t.^dtrack

no t:track|t in t.^utrack

one t:track|(track-t) in t.^utrack and no t.dtrack
and t.num=5

all t,p:track|t!=p and
t.dtrack=p <=> p.utrack=t

all t:track|some t.dtrack <=>
t.dtrack.num=t.num.add[1]
}

check
{
no t:track|t.utrack=t.dtrack
}
pred p{
some track.utrack
}
run p for exactly 5 track ,exactly 1 strack,5 int,2 train


