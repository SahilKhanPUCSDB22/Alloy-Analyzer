sig node
{
child: set node
}

fact{
one n:node|(node-n) in n.^child

no n:node|
n in n.^child

no n:node|
n in n.child

no n1,n2:node|
n1!=n2 and some n1.child&n2.child
}

pred p{}

run p for exactly 10 node
