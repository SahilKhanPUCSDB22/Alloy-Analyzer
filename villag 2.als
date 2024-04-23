one sig village
{
have :set cont ,
//next : lone village
}
{
#have=3
}

abstract sig cont
{
has :set character
}

sig boat extends cont{}
{
#has < 3
#boat=1
}

sig end extends cont{}
{
#has < 5
#end=2
}

abstract sig character{}
one sig man,lion,grass,sheep extends character{}

fact f
{
no c:cont ,d:cont |c!=d and some c.has & d.has

all e :end | 
sheep in e.has and lion in e.has => man in e.has

all e :end | 
sheep in e.has and grass in e.has => man in e.has

all c :character |
c in boat.has => man in boat.has

all ch:character | ch in cont.has
}

pred p
{

}
run p// for exactly 7 village , 3 cont , 4 character
