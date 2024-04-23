open util/ordering[village]

fact
{
first.end1=char and
no first.end2 and 
no first.boat

first.dir=left

/*no v:village |all c:char| let rest=c-m|
rest in v.boat and m not in v.boat*/

}

sig village
{
end1,end2,boat : set char,
dir : one d
}

{
#end1 <5
}

abstract sig d{}
one sig left,right extends d{}

fact
{
no v:village |
some v.end1 & v.end2 & v.boat

/*no v:village , c:char , vn:v.next |
c in v.end1 and c in vn.end2*/

/*all v:village , c:char |
c in v.boat => m in v.boat 
*/
}


abstract sig char{}
one sig m,s,g,l extends char{}

pred cross[from,fromn,to,ton:set char]
{
one char:from |
fromn=from - m - char
ton=to + m + char
}

fact
{
all v:village , v2 : v.next |

m in v.end1 => v2.dir=left and
cross[v.end1 , v2.end1 , v.boat , v2.boat]

else m in v.boat and v.dir=left => v2.dir=right and
cross[v.boat , v2.boat , v.end2 , v2.end2]

else m in v.boat and v.dir=right => v.dir=left and
cross[v.boat,v2.boat,v.end1,v2.end1]

else m in v.end2 => v2.dir=right and 
cross[v.end2 , v2.end2 , v.boat , v2.boat]
}

run {last.end2=char}
