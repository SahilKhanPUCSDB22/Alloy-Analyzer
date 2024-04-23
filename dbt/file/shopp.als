sig type
{
description :one String,
stock:one Int
}
{
stock >=0
}

sig product
{
prodtype: one type,
gdownid: one godown,
avail: one Int
}
{
avail=0 or avail=1
}

sig godown
{
loc:one city
}

sig city{info :one inf } 

sig inf{}

sig customer
{
name : one cust,
loc : one city
}

sig cust{}

sig order
{
custt : one customer,
prod : one type,
quan : one Int,
date : one Int,
status: one stat
}
{
quan>0
date>0
}

fact
{
all c:customer| order = c.~custt => 
#order=4 and order.custt=c
}

abstract sig stat{}
one sig ordered,shipped,delivered extends stat{}

sig courier
{
name : one cour,
loc : one city,
stats: one Int
}
{
stats=0 or stats=1
}

sig cour{}

sig deliveries
{
ord:one order,
prod:one product,
god:one godown,
couur:one courier,
status:one st,
date:one Int
}
{
date>0
}
abstract sig st{}
one sig Picked,Delivered extends st{}

fact
{
all c:customer|some o:order|o.custt=c

all t:type|some o:order|o.prod=t

all c:city|some g:godown|g.loc=c
all c:city|some cu:customer|cu.loc=c 
all c:city|some cou:courier|cou.loc=c

all o:order|some d:deliveries|
d.ord=o

all p:product|some d:deliveries|
d.prod=p

all g:godown|some d:deliveries|
d.god=g

all c:courier|some d:deliveries|
d.couur=c

all c:cour|some cc:courier|cc.name=c

all c:cust|some cc:customer|cc.name=c

all t:type|some p:product|p.prodtype=t

all o:order|some d:deliveries|d.ord=o
}

pred p{}

run p for exactly 6 type ,exactly 35 product ,exactly 8 godown ,
exactly 5 city ,exactly 5 inf , exactly 20 customer , 
exactly 14 cust , exactly 16 courier ,exactly 80 order ,
exactly 130 deliveries, exactly 8 String , 4 Int
,exactly 14 cour
