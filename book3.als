//every book must have atleast 10 pages and exactly one cover
sig page{}
sig cover{}
sig book
{
pages : set page ,
covers : one cover
}
{
#pages > 9
}

assert a
{
no b:book | #b.pages < 10 and no b.covers
}

check a for 5

