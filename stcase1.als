sig stcase{
has : some stair ,
step : person one -> one stair
}
fact f{
//all s:stair | one st:stcase | s in  st.has
all s:stair | some st :stcase | all p :person | st.step=p->s implies s in st.has and st.has=s
}
sig person{}
sig stair{}
//sig minute{}

check 
{ 
no st :stcase , s :stair , p1 :person , p2 :person | p1!=p2 and st.step=p1->s and st.step=p2->s 
} for 20 stcase , 20 stair , 20 person
pred p {}

run p for exactly 2 stcase , 6 stair , 4 person
