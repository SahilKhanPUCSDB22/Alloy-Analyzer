/*sig minute{
has : set seconds
}*/

sig seconds{}

/*fact f
{
all m:minute| #m.has < 61
}*/

one sig case
{
contains : some stairs
}

sig stairs
{
step : person set -> some seconds
}
{
#person <3
}
fact f
{
all p:person , se:seconds , st1:stairs,st2 :stairs |
st1!=st2 and
st1 in case.contains and st2 in case.contains and
p->se in st1.step implies p->se not in st2.step 

all s:stairs | one c:case | 
s in c.contains

}

check d
{ 
no p1:person , st:stairs |
st.step=p1->seconds and #p1->seconds >9
} for 10 seconds, 1 person , 1 case , 1 stairs
sig person{}

pred p{}
run p for 3 seconds,exactly 2 person,1 case,exactly 1 stairs

