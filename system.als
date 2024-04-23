sig system
{
has : some parts
}

abstract sig parts{}
sig cpu,hdd extends parts{}

fact{
all p:parts |some s:system| p in s.has
all s:system |some c: cpu| c in s.has
all s:system | some h:hdd| h in s.has
all h:hdd,s:system |let r=(system-s)|
h in s.has and h not in r.has
} 

pred p{}

run p for exactly 3 system ,exactly 8 parts
