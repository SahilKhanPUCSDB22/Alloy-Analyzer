open util/ordering[list]

sig list
{
disj inc,dec: lone Int
}

fact
{
all l:list|
some l.inc <=> no l.dec

all l:list|
some l.dec <=> no l.inc
}

pred p{
no l:list |
l.(inc+dec) >0
}

run p for exactly 2 list
