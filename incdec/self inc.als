sig list
{
next:lone list,
has : one el,
com:one cmd
}

abstract sig cmd{}
one sig i extends cmd{} 

sig el
{
ind : one Int
}

fact list
{
all l:list | l not in l.next

one l:list,e:el| l not in l.^next and
(list-l) in l.^next and e in l.has and 
//e.ind>0 and e.ind<6
e.ind=2

no l1,l2:list | l1!=l2 and
some l1.next&l2.next

no l1,l2:list | l1!=l2 and
some l1.has&l2.has
}

fact
{
all l1,l2:list ,
e1,e2:el , is:Int|
l1!=l2 and e1!=e2 and 
some l1.next and l1.next=l2 and
e1.ind=is and l1.com=i =>
add[l2,e2,is] 
}

pred add[l:list , e:el , i:Int]
{
i<5 =>
e.ind=i.add[1] and e in l.has
and some l.com 
else
e.ind=i
}

fact
{
all e:el |
e.ind>0 

all e:el|
e.ind<6
}
pred p{}
run p for exactly 4 list , 4 el , 2 cmd
