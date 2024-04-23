open util/ordering[el]

sig el
{
ind:one Int,
com:one cmd,
pcom:one cmd
}

abstract sig cmd{}
one sig inc,dec extends cmd{}

fact
{
first.ind=5 or first.ind=1 
some first.com
}

fact
{
all e:el|
e!=last and
e.ind=5 and e.com=dec => 
e.next.ind=4 and e.next.pcom=dec

all e:el|
e!=last and
e.ind=5 and e.com=inc =>
e.next.ind =5 and some e.pcom

all e:el |
e!=last and
e.ind >1 and e.ind<5 and e.pcom=dec =>
e.next.ind=e.ind.sub[1] and e.next.pcom=e.pcom

all e:el |
e!=last and
e.ind=1 and e.com=dec  =>
e.next.ind=1

all e:el |
e!=last and
e.ind=1 and e.com=inc =>
e.next.ind=2 and e.next.pcom=inc

all e:el , i:Int |
e!=last and e.ind=i and
i >1 and i<5 and e.pcom=inc =>
e.next.ind=(i).add[1] and e.next.pcom =e.pcom
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
run {last.ind=1} for 10 el
