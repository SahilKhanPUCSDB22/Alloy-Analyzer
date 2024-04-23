sig stcase{
has :some stair ,
step :person one -> one stair
}

fact f{
all s : stair | one st :stcase | s in st.has
}

sig stair{}
sig person{}

check 
{
no st :stcase , s :stair , p1 :person , p2 :person | p1!=p2 and st.step=p1->s and st.step =p2->s
} for 15 stcase , 50 stair , 100 person 

pred p{}

run p for 1 stcase , 4 stair , 10 person
