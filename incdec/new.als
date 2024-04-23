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

first.has.ind=5 or first.has.ind=1
some first.com
some first.pcom
}

fact
{
all l:list|
l.has.ind=5 and l.com=incr => 
same[l.next , l.has.ind , l.pcom]

all l:list|
l.has.ind=1 and l.com=decr => 
same[l.next , l.has.ind , l.pcom]

all l:list|
l.has.ind=5 and l.com=decr => 
dec[l.next , l.has.ind ,l.com]

all l:list|
l.has.ind=1 and l.com=incr => 
inc[l.next , l.has.ind,l.com]

all l:list|
l.has.ind>1 and l.com!=l.pcom => 
same[l.next,l.has.ind,l.pcom]

all l:list|
l.has.ind<5 and l.com!=l.pcom => 
same[l.next,l.has.ind,l.pcom]

all l:list|
l.has.ind>1 and l.has.ind!=5 and 
l.com=l.pcom and l.com=incr=> 
inc[l.next,l.has.ind,l.pcom]

//all l:list|
//l.has.ind<5 and l.has.ind!=1 and 
//l.com=decr and l.pcom=decr => 
//dec[l.next,l.has.ind,l.pcom]

}

pred inc[ln:list,i:Int, c:cmd]
{
ln.has.ind=i.add[1] and ln.pcom=c
}

pred dec[ln:list,i:Int, c:cmd]
{
ln.has.ind=i.sub[1] and ln.pcom=c
}

pred same[ln:list ,i:Int,c:cmd]
{
(ln.has).ind=i
and ln.pcom=c
}

pred p{} 
run p for 8
//run {last.has.ind =5}
