open util/ordering[up]
open util/ordering[down] 


sig up {u:lone p1,ui:one Int}
sig down{d:lone p2,di:one Int}

abstract sig person{}
//{
//#person=2
//}
one sig p1,p2 extends person {}

fact
{
all u:up|u!=last =>
u.next.ui=u.ui.add[1]
some first.u
some first.d
first.ui=1
first.di=5
all u:up|u!=last =>
u.next.ui=u.ui.add[1]
all d:down|d!=last =>
d.next.di=d.di.sub[1]
//no u1,u2:up|
//u1!=u2 and some u1.u&u2.u
//no d1,d2:down|
//d1!=d2 and some d1.d&d2.d
}

fact
{
all x:up|x!=last and x.u=p1 =>
p1 in x.next.u or p1 in x.next.next.u   

all x:down|x!=last and x.d=p2 =>
p2 in x.next.d or p2 in x.next.next.d

no u1:up,d1:down|u1!=last and d1!=last and
u1!=first and d1!=first and
p1 in u1.u and p2 in d1.d and
u1.ui=d1.di
}

pred p{}
run p for exactly 5 up , exactly 5 down  , 
2 person,5 int
