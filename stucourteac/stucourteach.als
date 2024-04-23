sig course
{
tea:set teacher,
enr:set student
}
{
#tea>0
#enr>0
}
sig project extends course{}
sig teacher{}
sig student{}

fact
{
all t:teacher|t in course.tea
all s:student|s in course.enr
}

check
{
no c:course|no c.tea
no c:course|no c.enr
}

pred p
{
no p1,p2:project|let x=p1.enr|p1!=p2 and
p2.enr=x  	
}
run p for 5 course,exactly 2 project ,3 teacher,4 student
