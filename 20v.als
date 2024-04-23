open util/ordering[vill]

fact {
end1.has=l and end1 in first.e1
}

sig vill
{
e1: end1 ,
e2: end2
}

abstract sig end{has:set l}
one sig end1,end2 extends end{}
sig l{}
one sig man,lion,grass ,goat extends l{}

fact
{
no m:l , v:vill ,e:end1 , ef:end2 |
v.e1=e and v.e2=ef and 
m in e.has and m in ef.has

all e:end |
grass in e.has and goat in e.has => man in e.has

all e:end |
lion in e.has and goat in e.has => man in e.has

}

/*fact f
{
all v:vill , vn:v.next , ea:end1 , eb:end2 |
v.e1=ea and v.e2=eb and
man in ea.has => p[v.e1 , vn.e1 , v.e2,vn.e2]
else
p[v.e2 , vn.e2 , v.e1 , vn.e1]
}

pred p[from , fromn , to , ton :set end]
{
one x : from.has {
fromn.has = from.has - x - man
ton.has = to.has + x + man
}
}*/
pred p{}

run p for exactly 2 vill , 
exactly 2 end, exactly 4 l
