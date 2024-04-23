sig array
{
has : set el
}

sig el
{
ind : one Int
}

fact
{
no e1,e2:el|
e1!=e2 and some e1.ind&e2.ind

some l:array| l.has=el

//no e:el | e in array.has and e.ind<0

some e:el|all a:array| e in a.has and e.ind=0 
} 

pred p{}

run p for exactly 1 array , exactly 9 el
