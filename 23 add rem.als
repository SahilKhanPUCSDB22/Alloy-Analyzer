open util/ordering[s]

sig s
{
has : set e
}

sig e{}

pred add [ sb , sa : set e , x :e]
{
sa=sb+x
}


pred rem [ sb , sa : set e , x :e]
{
sa=sb-x
}

pred find [st:set e , x:e]
{
x not in st
}

fact
{
all a:s , an:s.next , x:e | 
find[s.has,x] => add[a.has,an.has,x]
else rem[a.has,an.has,x]
}

/*fact
{
no st:s , sn:st.next , x:e|
x in st.has and x not in sn.has
} */

run {last.has=e}
