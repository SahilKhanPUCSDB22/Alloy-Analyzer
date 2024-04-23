open util/ordering[sett]

fact
{
first.has=elts
}

sig sett
{
has : set elts
}

sig elts{}

pred add[s1,s2 :sett , x: elts]
{
x not in s1.has =>
s2.has=s1.has + x

else 
s2.has=s1.has
}

check
{
all s:sett , s1:s.next , x:elts |
x not in s.has and
add[s,s1,x] => x in s1.has
}


check
{
all s:sett , s1:s.next , x:elts |
x in s.has and
add[s,s1,x] => x in s1.has
}

//run add for exactly 2 sett, exactly 5 elts
