sig list
{
has : some el
}
{
#has=2
}

sig el
{
index : one Int
}

fact
{
no l1,l2:list | l1!=l2 and
some l1.has&l2.has

no e1,e2:el ,l:list | 
e1!=e2 and
e1 in l.has and e2 in l.has and
some e1.index & e2.index

el in list.has

no e:el|e.index<0

//all l1,l2:list , e1,e2:el , i:Int|
//l1!=l2 and e1!=e2 and
//e1 in l1.has and e1.index=i =>
//e2 in l2.has and e2.index=i.add[1]

all l1:list , e1:el , i:Int|
some ll:list , e2:el, j:Int|let l2=ll|
l1!=l2 and e1!=e2 and
e1 in l1.has and e1.index=i <=>
j=i.add[1] and
e2 in l2.has and e2.index=j

}


pred p{}
run p for exactly 2 list , exactly 4 el

