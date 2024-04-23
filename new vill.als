abstract sig living{}
sig lion,person,sheep,grass extends living{}

abstract sig container{has:set living}
sig boat,end extends container{}

fact cap
{
#boat.has < 3
#end.has < 5
all e:end , r:end | no e.has & r.has
}

sig village{contains:set container}
{
#contains=3
}
fact v
{
one b:boat | b in village.contains
}

pred p{}
run p for exactly 1 village, 
exactly 3 container,
exactly 4 living
