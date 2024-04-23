sig minutes
{
has :set seconds
}
/*{
#has < 61
}*/

fact f{
all m:minutes,n:minutes ,s:seconds |
m!=n and  s in m.has => s not in n.has
}

sig seconds{}

/*sig stairs{}

sig stcase
{
step : person set -> one stairs -> set minutes
}

sig person{}
*/
pred p{}

run p for exactly 1 minutes ,exactly 70 seconds
