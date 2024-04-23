open util/ordering[c]


sig c
{
s1,s2,res : set e
}

sig e{}

fact 
{
no first.res and some first.s1 and
some first.s2
}

fact
{
all i:c , n:i.next | 
union[c.s1,n.s1,c.s2,n.s2,c.res,n.res]
}

pred union[s1b,s1a,s2b,s2a,resb,resa : set e]
{
all x:e | x in s1b => x in resa
all y:e | y in s2b => y in resa
s1a=s1b
s2a=s2b
}

fact 
{
all i:c , n:i.next ,x:e|
x not in i.s1 and x not in i.s2 =>
x not in n.s1 and x not in n.s2 and
x not in n.res
}

fact
{
no i:c , n:i.next , x:e |
x not in i.s1 and x in n.s1

no i:c , n:i.next , x:e |
x not in i.s2 and x in n.s2
}

fact
{
all i:c , n:i.next , x:e |
x in n.res => x in i.s1 and x in n.s1
or
x in i.s2 and x in n.s2
}

pred p{}

run p for exactly 2 c , exactly 6 e
