//a book should have atleast one chapter , 
//each chapter must have atlease three pages,
//each page must have something written on it 

sig page{}
sig content{}
sig chapter{}
sig book
{
has  : set chapter -> set page -> some content
}
{
#chapter > 0 
#page > 2
}

check {
no b : book | #b.has -> chapter <= 0 
no b : book | #b.has -> chapter -> page < 3
} for 4

pred p {}
run p for exactly 1 book , 2 chapter , 3 page , 4 content
