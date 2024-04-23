open util/ordering[sem]

sig msc
{
s : set sem
}
{
#s=4
}

sig sem{}

pred p{}
run p for exactly 1 msc, exactly 4 sem
