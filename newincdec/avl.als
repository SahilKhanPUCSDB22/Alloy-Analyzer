open util/integer

sig node
{
child: set node,
num : one Int
}

fact{
one n:node|(node-n) in n.^child

all n:node| #n.child<3

no n:node|
n in n.^child

no n:node|
n in n.child

no n1,n2:node|
n1!=n2 and some n1.child&n2.child 
}

fact height
{
all n:node|
no n.child <=> n.num=(0)

all n:node|#n.child=1 =>
n.num=n.child.num.add[1]

all n1,n2:node|
n1!=n2 and
n1.~child=n2.~child =>
add[(n1.~child.num),(n1.num.add[1]),(n2.num.add[1])]
}

fact
{
no n1,n2:node|n1!=n2 and
n1.~child=n2.~child and
n1.num.sub[n2.num]>1

no n:node|
#n.child=1 and n.num > 1
}

check
{
all n1,n2:node|
n1!=n2 and
n1.~child=n2.~child => n1.~child.num=n2.~child.num

no n:node|
#n.child=1 and n.child.num >1

no n:node|
n.num<0
} for 30 node

pred add[n,i,j:Int]
{
n=i.add[j]
}
pred p{}

run p for exactly 12 node , 7 int
