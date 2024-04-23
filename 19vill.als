open util/ordering[village]

sig village
{
contains : set cont,
dir:one d
}

abstract sig d{}
one sig l,r extends d{}

abstract sig cont{has : set char}
sig end extends cont{}

abstract sig char{}
one sig man extends char{}

fact 
{
all c1:cont , c2:cont | c1!=c2 and
c1 in first.contains and 
c2 in first.contains and
char in c1.has and
no c2.has and 
first.dir=l
} 



