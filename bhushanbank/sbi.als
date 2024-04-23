open util/ordering[bank]

sig bank
{
has : set ac
}
{
#has=3
}

sig ac
{
n: lone ac,
bal : one Int,
//it: one Int,
//ot:one Int,
tr:set ac
}

fact 
{
all a:ac|
a in last.has => no a.tr

all b:bank,a:ac|
a in b.has and some a.tr =>
a.tr in b.has

all a:ac,b:bank,x:Int|b!=last and
a in b.has and a.bal=x and #a.tr=0 and a not in 
(b.has-a).tr => a.n.bal=x

//some x:ac|x in first.has and #x.tr=2 

no b:bank|b.has.bal<0

first.has.bal=10
//first.has.it=0
//first.has.ot=0

all b:bank,a:ac|
b!=last and a in b.has =>
some a2:ac|
a2 in a.n and a2 in b.next.has

no a:ac|
a in a.n

no b:bank|
some b.has&(bank-b).has

no a:ac|
some a.n&(ac-a).n

all a:ac|
a in last.has => no a.n

no a:ac|
a in a.tr

all bn:bank,a:ac,x:Int|bn!=last and
a in bn.has and some a.tr and x=#a.tr => 
a.n.bal=a.bal.sub[x] and
a.tr.n.bal=a.tr.bal.add[1] 
}


pred p{}
//pred q{}
//run q for exactly 1 bank , 4 ac , 9 int
run p for exactly 3 bank , exactly 9 ac,7 int
