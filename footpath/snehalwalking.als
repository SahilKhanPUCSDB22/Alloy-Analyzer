open util/ordering[lane]

sig lane
{
lane1:set people,
lane2:set people,
lane3:set people
}

sig people
{
disj inc,dec:lone Int
}

fact
{
all p:people | #p.(inc+dec)=1

all l:lane , l1:l.next | 
l1.(lane1+lane2+lane3).inc=l.(lane1+lane2+lane3).inc.add[1] 
and l1.(lane1+lane2+lane3).dec=l.(lane1+lane2+lane3).dec.sub[1] 
 
no l:lane|
some l.lane1&l.lane2&l.lane3

}

pred p{}

run p for exactly 4 lane, exactly 8 people
