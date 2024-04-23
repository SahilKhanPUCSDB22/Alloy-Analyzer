open util/ordering[list]

fact
{
some first.has
}


sig list
{
has : set ele
}

sig ele
{
next : lone ele ,
prev : lone ele
}

fact
{
no e:ele | e in e.next and e in e.prev

all f:ele | f not in f.^next and f not in f.^prev 

no e,r:ele | e!=r and
e.next=r and r.next=e

no e1,e2:ele | e1!=e2 and 

some e1.next & e2.next and
some e1.prev & e2.prev

all e1,e2:ele |e1!=e2 and e1.next=e2 <=> e2.prev=e1
}

fact list
{
all e:ele ,l:list| e in l.has => e.next in l.has and
e.prev in l.has

all l:list , e:ele | e in l.has and #l.has>1 =>
some e.next or some e.prev

all e:ele | e not in list.has <=> no e.next and no e.prev

one f,lt:ele|all l:list |f in l.has and 
lt in l.has and no lt.next and no f.prev and
lt in f.^next and f in lt.^prev
}

pred p {}

run p for exactly 5 ele , exactly 1 list
