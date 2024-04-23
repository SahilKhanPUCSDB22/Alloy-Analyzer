open util/ordering[list]
open util/ordering[el]

sig list
{
has : set el
}

sig el
{
index : one Int
}

fact
{
some first.has and #first.has=2
}

fact
{
all l:list , ln:l.next , 
e:el, en:e.next , i:Int |
e in l.has and e.index=i => 
inc[l.has,ln.has,en,i]
}

pred inc[lb,ln:set el, en:set el , i:set Int]
{
en.index=i.add[1] and en in ln and en not in 
lb
}

pred p{}

run p for exactly 2 list , exactly 4 el
