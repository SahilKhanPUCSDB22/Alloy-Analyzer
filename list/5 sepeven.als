open util/integer
open util/ordering[list]

fact
{
some first.c
}

sig list
{
c : set el
}

sig el{
has : one data,
index : lone Int
}

sig data{}

fact
{
all l:list , ln:l.next , e:el |
e in l.c => e in ln.c

all e,f:el,l:list | e!=f and
e in l.c and f in l.c <=>
e.index !=f.index
}

fact
{
all l:list , ln:l.next |
ind[l.c , ln.c]
}

pred ind[lb,la : set el]
{
all x:lb , i:Int |
x.index=i => x in la and
x.index=i+1 
}

fact 
{
all e:el |
e in list.c => some e.index
}

pred p{}

run p for exactly 2 list ,
exactly 4 el , exactly 2 data ,4 int
