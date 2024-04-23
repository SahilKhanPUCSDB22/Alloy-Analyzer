abstract sig n{}

one sig null extends n{}

sig node extends n{
next:one n,
index : Int ,
data : one data
}

sig data{}

fact
{
no n1,n2:node , i:Int|
n1!=n2 and
i in n1.index and i in n2.index
}

fact
{
node not in node.next
one n:node | n.next=null
no n:node,m:node | m!=n and m.next=n and n.next=m
one first:node|
let r=(node-first) |
first.index=0 and 
first not in first.^next and
r in first.^next
}

/*fact
{
all n1,n2:node , i:Int | n1!=n2 and 
null not in n1.next and null not in n2.next and
n2 in n1.next and n1.index =i
=> n2.index = i+1
}*/

pred p{}

run p for exactly 6 n , exactly 6 data , 3 int
