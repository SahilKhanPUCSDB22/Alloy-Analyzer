open util/ordering[list]
open util/integer

fact
{
some first.c
}

fact
{
all e:elt ,l:list ,ln:l.next |
e in l.c => e in ln.c

all l:list , ln:l.next , e:elt | e not in l.c
=> add[l.c,ln.c,e]
}

pred add[lb,la :set elt , e: set elt]
{
e in la => all x:la | x.index >=e.index => 
x.index=x.index + 1
}

check
{
all e:elt , l:list , ln:l.next |
e not in l.c and add[l.c , ln.c , e]=> 
e in ln.c
}

sig list
{
c : set elt
}

sig elt{
has :one data,
index :one Int
}
sig data{}

fact
{
all e1,e2:elt , l:list|
e1!=e2 and e1 in l.c and 
e2 in l.c => e1.index !=e2.index
}

pred p{}
run p for exactly 2 list , exactly 4 elt , 
2 data
