abstract sig animal{}

one sig a1,a2,a3 extends animal{}

abstract sig person {
oneanimal : one animal ,
hasanimal : some animal ,
friend : one person
}

one sig p1,p2,p3 extends person{}

pred show{}

run show

fun x :person->animal{
p1->a1 + p2->a2 + p3->a3
}

pred hanimal {
all p:person | some t:p.x | t in p.hasanimal
}

run hanimal

//write a pred to verify that somebody has a1 as 
//only hasanimal

pred alone{
some p:person | a1 in p.oneanimal
}

run alone{} 

pred a1oneanimal
{
some p:person | a1 in p.hasanimal
}

run a1oneanimal

pred ea
{
all p:person | a2 in p.hasanimal and 
a2 in p.oneanimal
}

run ea

pred tp
{
p3 in animal.~oneanimal
}

run tp

pred f
{
p2 in p1.^friend and p1.friend!=p2
}

run f

