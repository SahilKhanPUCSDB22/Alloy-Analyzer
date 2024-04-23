module rules

open util/ordering[train1]
open util/ordering[train2]
open util/ordering[track]

sig track
{
track1:set train,
track2:lone train,
seg:one Int
}
{
#track1 <3
}

abstract sig train
{
s:one Int,
signal:one sign
}
sig train1,train2 extends train{}

abstract sig sign{}
one sig green,red,null extends sign{}

fact
{
all t:train1|t=first => t.s=1
all t:train2|t=first => t.s=13

all t:track|t!=last =>
t.next.seg=t.seg

all t1:train1,t2:train2|
t1=first and t2=first =>
first.track1=t1+t2
and no first.track2

first.seg > 2 and first.seg <12
//first.seg=4

all t:track|
(#t.track1).add[(#t.track2)]=2
}

pred inc[t:train1]
{
t.next.s=t.s.add[1]
}

pred dec[t:train2]
{
t.next.s=t.s.sub[1]
}

pred p{}
run p for exactly 15 track,
exactly 15 train1 ,
exactly 15 train2 ,
3 sign, 
5 int

pred next[t:track,t1:train1,t2:train2]
{
t1!=last and t2!=last and t!=last 
}
