sig stream {
have : disj one degree}
abstract sig degree{}
one sig mca ,msc extends degree{}

sig batches{
bno : disj one Int
}
{
bno>-1
}

sig student{
rollno: one Int,
batch: one Int,
stream: one degree
}
{
rollno>0
}

sig courses{
cno :disj one Int,
cname: disj one coursename
}
{
cno>0
}

sig coursename{}

sig streamcourse{
ccode:one Int,
str:one degree,
sem : one Int
}
{
sem >0  and sem <5
}

sig courselist {
ccode: one Int,
sem : one Int,
year : one Int
}
{
ccode>0
sem >0 and sem <5
}

sig stucoureg{
rno: one Int,
cno:one Int,
yr: one Int,
sem: one Int
}
{
rno>0
yr>0
sem>0 and sem <5}

fact
{
no disj s1,s2:stucoureg|s1.rno=s2.rno and
s1.yr=s2.yr and s1.sem=s2.sem and s1.cno=s1.cno

//no s:stucoureg|some st:student|s.rno!=st.rollno and
//s.yr!=st.batch

all s:stucoureg|let y=student.batch| 
let r=student.rollno|s.rno in r and s.yr in y

all s:stucoureg|let c=courselist.ccode| 
let y=courselist.year|s.cno in c and s.yr in y

//some s:student|all st:stucoureg|
//st.rno=s.rollno and st.yr=s.batch

all s:stucoureg|some c:courselist|s.yr=c.year and
s.sem=c.sem and s.cno=c.ccode

all s:student|let i=batches.bno|s.batch in i

no disj s1,s2:student|s1.rollno=s2.rollno and
s1.batch=s2.batch and s1.stream=s2.stream

all s:streamcourse|let c=courses.cno|s.ccode in c

no disj s1,s2:streamcourse|s1.ccode=s2.ccode and
s1.str=s2.str 

all s:streamcourse|some c:courselist|
c.ccode=s.ccode and s.sem=c.sem

no disj c1,c2:courselist|c1.ccode=c2.ccode and
c1.sem=c2.sem and c1.year=c2.year

all c:courselist|let x=batches.bno| c.year in x
}

check
{
no s:student|all i:batches.bno|s.batch not in i
}

run {} for exactly 2 stream,exactly 5 batches , 
exactly 10 student,exactly 7 courses, 
exactly 12 streamcourse,exactly 15 courselist,
exactly 20 stucoureg,exactly 7 coursename,5 int
