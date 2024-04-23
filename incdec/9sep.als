open util/ordering[list]
open util/ordering[el]

fact
{
first.com=inc 
}

sig list
{
com:one cmd , 
has : one el
}

abstract sig cmd{}
one sig inc,dec extends cmd{}

sig el
{
ind:one Int
}

fact
{
all e:el , en:e.next , l:list , ln:l.next|
e in l.has and en in ln.has

all e:el , en:e.next , l:list , ln:l.next,i:Int|
e in l.has and e.ind=i and l.com=inc=>
incr[ln,en,i]
}

pred incr[ln:set list, en:el , i:Int]
{
en in ln.has and en.ind=i.add[1]
and some ln.com
}

pred p{}

run p for 2
