sig time{}
sig book
{
issued : student lone -> set time
}

sig student {}

sig library
{
has : some book
}

fact f
{
all b : book , s1: student , s2 : student , t: time| b.issued=s1->t and b.issued=s2->t implies s1=s2
some l : library  | all b : book | b in l.has
/*added fact*/ some b : book | all l : library | b in l.has and #b.issued=0 
}

check {
no b : book , s1 : student , s2 : student , t : time |s1 != s2 and b.issued=s1->t and b.issued=s2->t
}

pred p{}
run p for 2 library ,8 book , 2 student , 2 time  
