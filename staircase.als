sig staircase{have : set stair,
next : lone staircase}

sig stair{
contain : set man}
{
#contain<3
}
sig man{}
fact
{
all s:staircase , s1:s.next | 
all s2:stair ,m:man |
s2 in s.have and m in s2.contain => s2 in s1.have and m not in s2.contain
all s:stair ,s1:staircase | s in s1.have }
