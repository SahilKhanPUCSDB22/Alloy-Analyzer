open util/ordering[el]

sig el
{
ind: one Int,
pcom:one cmd,
com:one cmd
}

abstract sig cmd{}
one sig inc,dec extends cmd{}

fact
{
first.ind=5 //or first.ind=1
}

fact
{
all e:el|
e.ind=5 => ac15[e.ind,e.com,e.next]


all e:el|
e.ind=1 => ac15[e.ind,e.com,e.next]

all e:el|
e.ind<5 and e.ind>1 => acbw[e.ind , e.pcom ,e.next]
}

pred ac15[i:Int,c:cmd,e:el]
{
c=inc and i=5 => e.ind=i and some e.pcom 
c=dec and i=5 => e.ind=i.sub[1] and e.pcom=dec

c=dec and i=1 => e.ind=i and some e.pcom
//c=inc and i=1 => e.ind=i.add[1] and e.pcom=inc
}

pred acbw[i:Int,c:cmd,e:el]
{
c=inc => e.pcom=inc and e.ind=i.add[1]
c=dec => e.pcom=dec and e.ind=i.sub[1]
}

run {last.ind=5} for 6 el
