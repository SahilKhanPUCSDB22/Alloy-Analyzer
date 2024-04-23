open util/ordering[el]
open util/ordering[list]

sig list
{
has : some el
}

sig el
{
index : one Int
}

fact
{
#first.has>0 
first.index=0
}

fact
{
no e:el , en:e.next |
some e.index & en.index

all e:el , en:e.next,i:Int|
all l:list , ln:l.next|
e in l.has and e.index=i <=>
en in ln.has and en.index =i.add[1]

all e:el , en:e.next |
en.index = e.index.add[1]
and e.index=en.index.sub[1]
} 

fact
{
no l:list , ln:l.next |
some l.has & ln.has
}


pred p {}

run p for exactly 4 el , exactly 2 list

