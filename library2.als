sig time{}
sig book{}
sig student{}
sig library{
has : some book ,
issue : book set -> set student -> set time
}
check 
{
no b : book , s1 : student , s2 : student , t: time , l : library | s1!=s2 and l.issue=b->s1->t and l.issue=b->s2->t
}

pred p {}

run p for exactly 1 library , 4 book , 1 student , 1 time
