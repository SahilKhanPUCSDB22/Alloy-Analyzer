abstract sig sem
{
has:set stu,
tcredit : one Int
}
{
tcredit=12
}

one sig sem1,sem2,sem3,sem4 extends sem{}

sig stu
{
credits: one Int,
n:one stu,
res:lone res
}
{
credits>=0 and credits<=12
}

abstract sig res{}
one sig pass,fail extends res{}

fact
{
//start with 10 students in sem 1
#sem1.has=5

//all students in sem1 will go to sem2 regardless the 
//credits
all s:stu|s in sem1.has => 
one x:stu|x in sem2.has and
s.n=x

all s:stu|s in sem2.has =>
one x:stu|x in sem1.has and
s.~n=x

//student has unique next state
no s:stu,se:sem|s in se.has
and some s.n & (se.has-s).n
//no student state repeats in multiple semisters
no s:sem|some s.has & (sem-s).has

all s,nx:stu|s in sem1.has and 
s.credits.add[s.n.credits]>sem1.tcredit 
and s.n=nx => one x:stu|x in sem3.has and
nx.n=x
}

pred p{}

run p for 4 sem , 2 res , exactly 15 stu , 5 int
