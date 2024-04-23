open util/ordering[el]

sig el
{
ind:one Int,
com :one cmd,
pcom :lone cmd
}

abstract sig cmd{}
one sig inc,dec extends cmd{}

fact
{
(first.ind=5 or first.ind=1)
no first.pcom  
all e:el|e!=first <=> some e.pcom
}

fact
{
all e:el,i:Int|
e!=last and
e.ind=i and i=5 and e.com=dec=> 
five[e.next,e.com,i]

all e:el,i:Int|
e!=last and
e.ind=i and i=5 and e.com=inc =>
same[e.next,e.com,i]

all e:el,i:Int|
e!=last and
e.ind=i and i=1 and e.com=dec =>
same[e.next,e.com,i]

all e:el,i:Int|
e!=last and
e.ind=i and i=1 and e.com=inc =>
on[e.next,e.com,i]

all e:el,i:Int |
e!=last and
e.ind=i and i>1 and i<5 =>
inc[e.next,e.pcom,i]

all e:el,i:Int |
e!=last and
e.ind=i and i>1 and i<5 and e.pcom=dec =>
dec[e.next,e.pcom,i]
}

pred five[en:el,c:cmd,i:Int]
{
en.ind=i.sub[1] and en.pcom=c
}

pred same[en:el,c:cmd,i:Int]
{
en.ind=i and en.pcom=c
}

pred on[en:el,c:cmd,i:Int]
{
en.ind=i.add[1] and en.pcom=c
}

pred dec[en:el,c:cmd,i:Int]
{
en.ind=i.sub[1] and en.pcom=dec
}

pred inc[en:el,c:cmd,i:Int]
{
en.ind=i.add[1] and en.pcom=c
}

check
{
no e:el| e.ind<1
no e:el| e.ind>5

all e:el|
e!=last and
e.ind!=1 and e.ind!=5 and e.com=inc and e.pcom=dec =>
e.ind.sub[e.next.ind]=1 and e.next.pcom=dec

all e:el|
e!=last and
e.ind!=1 and e.ind!=5 and e.com=dec and e.pcom=dec =>
e.ind.sub[e.next.ind]=1 and e.next.pcom=dec


all e:el|
e!=last and
e.ind!=1 and e.ind!=5 and e.com=inc and e.pcom=inc =>
e.ind.next.sub[e.ind]=1 and e.next.pcom=inc

all e:el|
e!=last and
e.ind!=1 and e.ind!=5 and e.com=dec and e.pcom=inc =>
e.ind.next.sub[e.ind]=1 and e.next.pcom=inc
}

pred p{}

run {last.ind=5} for 15 el
