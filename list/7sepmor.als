open util/ordering[list]

fact
{
some first.e
}

sig list
{
e: set el
}

sig el
{
has : one data,
index: one Int
}

sig data{}

fact
{
all e1,e2:el , l:list|
e1!=e2 and e1 in l.e and e2 in l.e =>
e1.index!=e2.index
}

fact
{
all l:list , ln:l.next , i:Int , x:el|
x in l.e and x.index=i =>
inc[l.e,ln.e , x ,i]
}

pred inc[lb,ln : set el , e:set el , i: set Int]
{
e in lb and e.index=i =>
e in ln and 
e.index=i.add[1]
} 

check
{
all l:list,ln:l.next , x:el , i:Int |
x in l.e and x.index=i and
inc[l.e,ln.e,x,i]=> x.index!=i
}

pred p{}

run p for exactly 4 el ,
exactly 2 list ,exactly 3 data
  
