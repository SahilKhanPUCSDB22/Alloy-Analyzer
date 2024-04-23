sig node
{
edge:set node,
d:one Int,
ft:lone tar
}
{
#node>1
}

abstract sig tar{}
one sig from,to extends tar{}

fact
{
no n:node|n.d<0
no n:node|n in n.edge
all n:node|n in n.edge.edge
one x,y:node|x.ft=from and y.ft=to and no (node-x-y).ft
}

pred p{}
run p for exactly 5 node
