open util/ordering[list]

/*fact
{
some first.l
}*/

/*pred add[lb,la:set el ,e:set el , ind:set Int ]
{
//e.index=i
//all x:el | x in lb => x in la 
//all x:el | x in lb and x.index > i =>
//x.index=x.index+1 and x in la and e in la 
one x:e , i:ind| x.index=i and la=lb+x
}*/

/*fact
{
all lb:list , la:lb.next , e:el |e in lb.l => 
e in la.l
}*/ 

fact
{
all lc:list , ln:lc.next|some i:Int , e:el |
e not in lc.l => add[lc.l , ln.l , e , i]
}

sig list
{
l :set el
}

sig el 
{
has: one data,
index : one Int
}

fact
{
all e:el | e in list.l <=> some e.index
}

fact
{
no e1,e2:el | e1!=e2 and
e1 in list.l  and e2 in list.l and
some e1.index & e2.index
}

sig data{}

pred p{}

run p for exactly 2 list , exactly 4 el  , 
exactly 3 data
