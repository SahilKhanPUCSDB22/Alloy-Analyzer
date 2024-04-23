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
s:one Int
}
sig train1,train2 extends train{}

fact
{
all t:train1|t=first => t.s=1
all t:train2|t=first => t.s=7

all t:track|t!=last =>
t.next.seg=t.seg

all t1:train1,t2:train2|
t1=first and t2=first =>
first.track1=t1+t2
and no first.track2

first.seg > 2 and first.seg <6
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
run p for exactly 7 track,
exactly 7 train1 ,
exactly 7 train2 , 
5 int

pred next[t:track,t1:train1,t2:train2]
{
t1!=last and t2!=last and t!=last 
}

fact
{
//before crossing
all t:track,t1:train1,t2:train2|
next[t,t1,t2] and t.track1=t1+t2 and
(t1.s < t.seg.sub[1] and t2.s > t.seg.add[1])=>
inc[t1] and dec[t2] and
t.next.track1=t1.next+t2.next and
t.next.track2=t.track2

//after crossing
all t:track,t1:train1,t2:train2|
next[t,t1,t2] and t.track1=t1+t2 and
(t1.s > t.seg and t2.s < t.seg)=>
inc[t1] and dec[t2] and
t.next.track1=t1.next+t2.next and
t.next.track2=t.track2

//both at same pt
all t:track,t1:train1,t2:train2|
next[t,t1,t2] and t.track1=t1+t2 and
(t1.s = t.seg.sub[1] and t2.s = t.seg.add[1])=>
(inc[t1] and dec[t2] and t.next.track1=t1.next and t.next.track2=t2.next) 
or
(inc[t1] and dec[t2] and t.next.track1=t2.next and t.next.track2=t1.next)

//one at side and one at parallel
all t:track,t1:train1,t2:train2|
next[t,t1,t2] and
t.track1=t1 and t.track2=t2 and
t1.s=t.seg =>
inc[t1] and dec[t2] and
t.next.track1=t1.next+t2.next and
no t.next.track2

all t:track,t1:train1,t2:train2|
next[t,t1,t2] and
t.track1=t2 and t.track2=t1 and
t2.s=t.seg =>
inc[t1] and dec[t2] and
t.next.track1=t1.next+t2.next and 
no t.next.track2

//one at switch other behind
all t:track,t1:train1,t2:train2|
next[t,t1,t2] and
t.track1=t1+t2 and
t1.s = t.seg.sub[1] and
t2.s > t.seg.add[1] =>
inc[t1] and dec[t2] and
t.next.track2=t1.next and
t.next.track1=t2.next

all t:track,t1:train1,t2:train2|
next[t,t1,t2] and
t.track1=t1+t2 and
t1.s < t.seg.sub[1] and
t2.s = t.seg.add[1] =>
inc[t1] and dec[t2] and
t.next.track2=t2.next and
t.next.track1=t1.next

//one crossed other behind switch
all t:track,t1:train1,t2:train2|
next[t,t1,t2] and
t.track1=t1 and t.track2=t2 and
t1.s < t.seg.sub[1] and
t2.s = t.seg =>
inc[t1] and t2.next.s=t2.s and
t.next.track2=t2.next and
t.next.track1=t1.next

all t:track,t1:train1,t2:train2|
next[t,t1,t2] and
t.track1=t2 and t.track2=t1 and
t1.s = t.seg and
t2.s > t.seg.add[1] =>
dec[t2] and t1.next.s=t1.s and
t.next.track2=t1.next and
t.next.track1=t2.next

//one crossed other at switch
all t:track,t1:train1,t2:train2|
next[t,t1,t2] and
t.track1=t1 and t.track2=t2 and
t1.s = t.seg.sub[1] and
t2.s = t.seg =>
inc[t1] and t2.next.s=t2.s and
t.next.track2=t2.next and
t.next.track1=t1.next

all t:track,t1:train1,t2:train2|
next[t,t1,t2] and
t.track1=t2 and t.track2=t1 and
t1.s = t.seg and
t2.s = t.seg.add[1] =>
dec[t2] and t1.next.s=t1.s and
t.next.track2=t1.next and
t.next.track1=t2.next
}
  
