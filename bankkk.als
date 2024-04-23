/*kids bank such that it contains money in 
the form of 
two , 5 , 10 rupee coins,each coin 
belongs to some bank
*/
open util/ordering[bank]

fact{
no first.has
}

abstract sig coin{}
sig two,five,ten extends coin{}

sig bank{
has : set coin
}

fact
{
all b:bank , bn:b.next |
remc[b.has,bn.has]
}

pred remc[b,bn : set coin]
{
one x:b | 
bn=b-x
}

pred add[b,bn : set coin]
{
one x:coin | x not in b.has => bn.has=b.has+x
}

/*fact
{
all c:coin | some b:bank | c in b.has
no b1,b2:bank | b1!=b2 and
some b1.has & b2.has
}*/

/*check
{
no b1,b2:bank , c:coin | b1!=b2 and
c in b1.has and
c in b2.has
}*/

//pred p{}
run {last.has=coin}// for exactly 5 bank ,exactly 4 coin
