open util/ordering[list]

sig list
{
has :one el,
com:one cmd
}

abstract sig cmd{}
one sig incr,decr,nothing extends cmd{}

sig el{
ind:one Int
}

fact
{
one l:list|l.com=nothing

last.com=nothing

el in list.has

no l1,l2:list|l1!=l2 and
some l1.has&l2.has

(first.has).ind <=5 and (first.has).ind >=1
some first.com
}

fact
{
all l:list ,i:Int|
(l.has).ind=i and l.com=incr => inc[l.next,i]

all l:list ,i:Int|
(l.has).ind=i and l.com=decr => dec[l.next,i]
}

pred inc[l:list,i:Int]
{
all e:el|
e in l.has and i<5 => e.ind=i.add[1]

all e:el|
e in l.has and i=5 => e.ind=i
}


pred dec[l:list,i:Int]
{
all e:el|
e in l.has and i>1 => e.ind=i.sub[1]

all e:el|
e in l.has and i=1 => e.ind=i
}

check
{
no e:el|e.ind>5
no e:el|e.ind<1

all l:list,ln:l.next,e1,e2:el,i:Int|
e1!=e2 and e1 in l.has and e1.ind=i
and e2 in ln.has and l.com=incr and 
inc[ln,i] and i!=5 
=>
e2.ind.sub[i]=1


all l:list,ln:l.next,e1,e2:el,i:Int|
e1!=e2 and e1 in l.has and e1.ind=i
and e2 in ln.has and l.com=decr and 
dec[ln,i] and i!=1
=>
i.sub[e2.ind]=1 

all l:list , ln:list.next , e1,e2:el |
e1!=e2 and 
e1 in l.has and 
(e1.ind != 5 and e1.ind !=1) and 
some l.com and
e2 in ln.has
and (inc[ln,e1.ind] or dec[ln,e1.ind]) =>
e2.ind !=e1.ind
}

pred p{}

//run p for exactly 2 list , exactly 2 el , 2 cmd

run {(last.has).ind=3} for exactly 6 list, 
exactly 6 el ,2 cmd 
