open util/ordering[state]

sig state
{
boxa,boxb:set Int
}

fact init
{
no first.boxb
#first.boxa=4
}

fact state_transition
{
all s:state| some s.next => move[s,s.boxa,s.boxb]
}

pred move[n:state,a:set Int,b:set Int]
{
one x:a | n.next.boxa=n.boxa-x and n.next.boxb=n.boxb+x
}

run {no last.boxa} for exactly 5 state
