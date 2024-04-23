open util/ordering[train1]
open util/ordering[train2]
open util/ordering[track]

sig track
{
track1:set train,
t1tr1sig:one sign,
t2tr1sig:one sign,
track2:lone train,
t1tr2sig:one sign,
t2tr2sig:one sign,
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

abstract sig sign{}
one sig null,side,green,red extends sign{}

fact
{
all t:train1|t=first => t.s=1
all t:train2|t=first => t.s=11

all t:track|t!=last =>
t.next.seg=t.seg

all t:track|t=first =>
t.t1tr1sig=null and
t.t2tr1sig=null and
t.t1tr2sig=null and
t.t2tr2sig=null

all t1:train1,t2:train2|
t1=first and t2=first =>
first.track1=t1+t2
and no first.track2 

first.seg > 4 and first.seg <8
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
run p for exactly 11 track,
exactly 11 train1 ,
exactly 11 train2 , 
5 int

pred next[t:track,t1:train1,t2:train2]
{
t1!=last and t2!=last and t!=last 
}

fact
{
//train up down movement
all t:track,t1:train1,t2:train2|next[t,t1,t2] and
t.track1=t1+t2 and
t1.s < t.seg.sub[1] and
t2.s > t.seg.add[1]  => inc[t1] and 
dec[t2] and t.next.track1=t1.next+t2.next

//one reaches signal zone before another
all t:track,t1:train1,t2:train2|next[t,t1,t2] and
t.track1=t1+t2 and
t1.s = t.seg.sub[3] and
t2.s > t.seg.add[3] =>
t.next.track1=t1.next + t2.next and
t.next.t1tr1sig=side and 
t.next.t2tr1sig=green

all t:track,t1:train1,t2:train2|next[t,t1,t2] and
t.track1=t1+t2 and
t2.s = t.seg.add[3] and
t1.s < t.seg.sub[3] =>
t.next.track1=t1.next + t2.next and
t.next.t1tr1sig=green and 
t.next.t2tr1sig=side

//both reach signal zone at the same time
all t:track,t1:train1,t2:train2|next[t,t1,t2] and
t.track1=t1+t2 and
t2.s = t.seg.add[3] and
t1.s = t.seg.sub[3] =>
t.next.track1=t1.next + t2.next and
t.next.t1tr1sig=red and 
t.next.t2tr1sig=side or
t.next.track1=t1.next + t2.next and
t.next.t1tr1sig=side and 
t.next.t2tr1sig=red

//before anyone reaches signal zone
all t:track,t1:train1,t2:train2|next[t,t1,t2] and
t.track1=t1+t2 and
t1.s<t.seg.sub[3] and
t2.s>t.seg.add[3] =>
t.next.track1=t1.next+t2.next and
t.next.t1tr1sig=null and 
t.next.t2tr1sig=null

//signal unchanged
all t:track,t1:train1,t2:train2|next[t,t1,t2] and
t.track1=t1+t2 and
t.t1tr1sig!=null and t.t2tr1sig!=null =>
t.next.track1=t1.next+t2.next and
t.next.t1tr1sig=t.t1tr1sig and 
t.next.t2tr1sig=t.t2tr1sig

}
  
