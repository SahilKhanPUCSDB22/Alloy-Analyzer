open util/ordering[el]

fact
{
first.com=dec
first.ind=1
}

sig el
{
com: one cmd,
ind: one Int
}

abstract sig cmd{}
one sig inc,dec extends cmd{}

fact
{
all e:el ,en:e.next, i:Int|
e.ind=i and e.com=inc and i<=5 => incr[en,i]
}

fact
{
all e:el ,en:e.next, i:Int|
e.ind=i and e.com=dec and i>=1 => decr[en,i]
}

pred incr[e:one el , i:one Int]
{
i<5 => e.ind=i.add[1]
i=5 => e.ind=i
}

pred decr[e:one el , i:one Int]
{
i>1=>e.ind=i.sub[1]
i=1=>e.ind=i
}

check
{
all e:el , en:e.next ,i:Int|
e.ind=i and incr[en,i] and i!=5=> en.ind > e.ind

all e:el , en:e.next ,i:Int|
e.ind=i and decr[en,i] and i!=1=> en.ind < e.ind
}

pred p{}
run p for exactly 10 el , 2 cmd
