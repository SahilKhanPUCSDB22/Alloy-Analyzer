open util/ordering[train1]
open util/ordering[train2]

abstract sig train
{
track:one trak,
segno:one Int,
stateno:one Int
}
sig train1,train2 extends train{}

fact
{
all t:train1|t=first <=> t.segno=1 and t.track=track1 
and t.stateno=1

all t:train2|t=first <=> t.segno=11 and t.track=track1
and t.stateno=1

all t:track2|t.seg >1 and t.seg <11

all t:train1|t!=last =>
t.next.stateno=t.stateno.add[1]

all t:train2|t!=last =>
t.next.stateno=t.stateno.add[1]
}

abstract sig trak{}
sig track1 extends trak{}
one sig track2 extends trak{seg:one Int}

pred p{}

run p for exactly 11 train1,exactly 11 train2,
2 trak,5 int

fact
{
all t:train1|t!=last and
t.track=track1 and t.segno < track2.seg.sub[1] =>
inc[t.next,t.segno,t.track]

all t:train1|t!=last and
t.track=track1 and t.segno >=track2.seg =>
inc[t.next,t.segno,t.track]
}

pred inc[t:train1,i:Int,tr:trak]
{
t.segno=i.add[1] and t.track=tr
}

pred dec[t:train2,i:Int,tr:trak]
{
t.segno=i.sub[1] and t.track=tr
}

fact
{
