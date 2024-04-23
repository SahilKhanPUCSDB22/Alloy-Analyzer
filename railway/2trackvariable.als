open util/ordering[track]
open util/ordering[train1]
open util/ordering[train2]

//**********signatures********************************//
sig track
{
track1:set train,
track2:lone train,
seg:one Int
}
{
#track1 <3
}

abstract sig pr{}
one sig y,n extends pr{} 

abstract sig train
{
s:one Int,
per:one pr
}

sig train1,train2 extends train{}
//**************preconditions and invariants***********/
fact
{
all t:train1|t=first => t.s=1
all t:train2|t=first => t.s=7

all t1:train1,t2:train2|
t1=first and t2=first =>
t1.per=y and t2.per=n or
t1.per=n and t2.per=y 

all t:track|t!=last =>
t.next.seg=t.seg

all t1:train1,t2:train2|t1!=last and t2!=last =>
t1.next.per=t1.per and t2.next.per=t2.per

all t1:train1,t2:train2|
t1=first and t2=first =>
first.track1=t1+t2
and no first.track2


first.seg > 2 and first.seg <6
//first.seg=4

all t:track|
(#t.track1).add[(#t.track2)]=2
}

//**********************predicates********************//
pred inc[t:train1]
{
t.next.s=t.s.add[1]
}

pred dec[t:train2]
{
t.next.s=t.s.sub[1]
}

pred next[t:track,t1:train1,t2:train2]
{
t1!=last and t2!=last and t!=last 
}

pred samet1[t1:train1]
{
t1.next.s=t1.s
}

pred samet2[t2:train2]
{
t2.next.s=t2.s
}
//***************assertions***************************//
check
{
no t:track,t1:train1,t2:train2|
t.track1=t1+t2 and 
t1.s=t2.s

no t:track,t1:train1,t2:train2|
t.track1=t1+t2 and 
t1.s=t2.s

no t:train|
t.per=n and t in track.track2
} for 20 train1, 20 train2 , 20 track , 2 pr

//*********************run for instance***************/
pred p{}

run p for exactly 7 train1, exactly 7 train2,
exactly 7 track,
exactly 2 pr

//**********************state transition***************/
fact
{
all t:track,t1:train1,t2:train2|next[t,t1,t2] and
t.track1=t1+t2 and
t1.s < t.seg.sub[1] and
t2.s > t.seg.add[1] =>
inc[t1] and dec[t2] and
t.next.track1=t1.next+t2.next

//bringing to same point
all t:track,t1:train1,t2:train2|next[t,t1,t2] and
t.track1=t1+t2 and
t1.per=n and t1.s=t.seg.sub[1] and
t2.s > t.seg.add[1] =>
dec[t2] and samet1[t1] and
t.next.track1=t1.next+t2.next  

all t:track,t1:train1,t2:train2|next[t,t1,t2] and
t.track1=t1+t2 and
t2.per=n and t2.s=t.seg.add[1] and
t1.s < t.seg.sub[1] =>
inc[t1] and samet2[t2] and
t.next.track1=t1.next+t2.next

//about to cross
all t:track,t1:train1,t2:train2|next[t,t1,t2] and
t.track1=t1+t2 and
t1.s=t.seg.sub[1] and t2.s=t.seg.add[1] and t1.per=y => 
inc[t1] and samet2[t2] and 
t.next.track1=t1.next+t2.next

all t:track,t1:train1,t2:train2|next[t,t1,t2] and
t.track1=t1+t2 and
t1.s=t.seg.sub[1] and t2.s=t.seg.add[1] and t2.per=y => 
dec[t2] and samet1[t1] and 
t.next.track1=t1.next+t2.next

//crossing happens
all t:track,t1:train1,t2:train2|next[t,t1,t2] and
t.track1=t1+t2 and
t1.s=t.seg and t2.s>=t.seg.add[1] and
t1.per=y => inc[t1] and dec[t2] and 
t.next.track1=t2.next and t.next.track2=t1.next

all t:track,t1:train1,t2:train2|next[t,t1,t2] and
t.track1=t1+t2 and
t2.s=t.seg and t1.s<=t.seg.sub[1] and
t2.per=y => inc[t1] and dec[t2] and 
t.next.track1=t1.next and t.next.track2=t2.next

//move ahead
all t:track,t1:train1,t2:train2|next[t,t1,t2] and
(t.track1=t1 and t.track2=t2) =>
inc[t1] and dec[t2] and t.next.track1=t1.next and
t.next.track2=t2.next

all t:track,t1:train1,t2:train2|next[t,t1,t2] and
(t.track1=t2 and t.track2=t1) =>
inc[t1] and dec[t2] and t.next.track1=t2.next and
t.next.track2=t1.next

//*****************************************************
//
all t:track,t1:train1,t2:train2|next[t,t1,t2] and
t.track1=t1+t2 and
t1.s=t.seg.sub[1] and
t2.s > t.seg.add[1] and
t1.per=y =>
inc[t1] and dec[t2] and
t.next.track1=t1.next+t2.next

all t:track,t1:train1,t2:train2|next[t,t1,t2] and
t.track1=t1+t2 and
t2.s=t.seg.add[1] and
t1.s < t.seg.sub[1] and
t2.per=y =>
inc[t1] and dec[t2] and
t.next.track1=t1.next+t2.next
}
