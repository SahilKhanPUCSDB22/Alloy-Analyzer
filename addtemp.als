sig st
{
has : set e ,
next : one st
}

fact
{
no s:st | s.next=s and s in s.^next
}

sig e{}

fact
{
all s:st , x:e | x not in s.has => add[s,s.next,x]
}

pred add[s,sn :st , x:e]
{
sn.has=s.has+x
}

run add for exactly 2 st , exactly 2 e
