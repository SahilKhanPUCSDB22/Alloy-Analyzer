open util/ordering[sett]

fact
{
first.has=elements
}

sig sett
{
has : set elements
}

sig elements{}

pred remove[s,s1 :sett , x:elements ]
{
x in s.has => 
s1.has = s.has - x

else
s1=s
}

check
{
all s:sett , s1:s.next , x:elements | 
x in s.has and
remove[s,s1,x]=>
x not in s1.has
}

check
{
all s:sett , s1:sett.next , x:elements |
x not in s.has and 
remove[s,s1,x] => 
x not in s1.has and x not in s.has
} 


run remove for exactly 2 sett , exactly 3 elements

/*fact
{
all s:sett , x:elements | x in s.has => 
remove[s,s.next,x]
}
pred p{}

run p for exactly 1 sett ,exactly 1 elements
*/
