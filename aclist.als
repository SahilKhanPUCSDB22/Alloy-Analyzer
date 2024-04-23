open util/ordering[list]

fact
{
first.has=ele
}

sig list
{
has : some ele
}

sig ele
{
index :one Int,
data :one data,
next :lone ele
}

sig data{}

fact
{
no e:ele | e in e.next
one f:ele |all e:ele|let r=e-f| 
f not in f.^next and r in f.^next and f.index=0 
one e:ele | no e.next

/*all e1,e2:ele | e1!=e2 and e1.next=e2 
<=> e2.index > e1.index*/ }

fact
{
no e1,e2:ele |e1!=e2 and
some e1.index & e2.index
}

fact
{
no e1,e2 : ele | e1!=e2 and
e1.index > e2.index and e1.next=e2
}

pred p{}

run p for exactly 1 list , exactly 8 ele , 
exactly 2 data ,4 int
