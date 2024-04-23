open util/ordering[list]

sig list
{
has : one el,
com: one cmd,
pcom: one cmd
}

sig el
{
ind :one Int
}

abstract sig cmd{}
one sig incr,decr extends cmd{}

fact
{
no l1,l2:list|l1!=l2 and
some l1.has&l2.has

first.has.ind=5
first.com=incr
}

fact
{
all l:list,ln:l.next,i:Int|
l.has.ind=i and l.com=incr and i=5  => 
ln.has.ind=i
}

pred p{}
run p for 2


