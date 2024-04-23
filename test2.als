open util/ordering[cart1]
open util/ordering[cart2]

one sig webstore
{
has : some items
}
{
has=items
}

sig items{}

abstract sig user
{
select:set items,
carts:set cart
}
one sig user1,user2 extends user{}

abstract sig cart
{
has:set items
}

sig cart1,cart2 extends cart{}

fact
{
all c:cart1| c in user1.carts
all c:cart2| c in user2.carts

no u:user|some u.carts.has & u.select

all c:cart1|c=first =>no c.has
all c:cart2|c=first =>no c.has
}

fact
{
all c:cart1|c = first and c in user.carts =>
c.next.has=c.has+user.select

all c:cart2|c = first and c in user.carts =>
c.next.has=c.has+user.select
} 
pred p{}
run p for 1 webstore , exactly 5 items , 
exactly 2 user ,exactly 2 cart1,exactly 2 cart2
