open util/ordering[semister]

sig msc
{
has : set semister
}
{
#has=4
}

fact
{
first.has=student //and no (semister-first).has

all s:semister , st:student|s!=last and
st in s.has and st.credits > 5 <=> st in s.next.has
}

sig semister
{
has : set student
}

sig student
{
credits:one Int
}

pred p{}

run p for exactly 1 msc , 4 semister , 
exactly 4 student
