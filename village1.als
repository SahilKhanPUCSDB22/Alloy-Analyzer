abstract sig living{}
abstract sig container { contains: set living}
one sig lion extends living{}

one sig sheep extends living{}

one sig person extends living{}
one sig grass extends living {}

sig end  extends container {}
one sig boat extends container {} 
fact {
   no l:living | no c1: container| no c2: container |
     c1 != c2 and l in c1.contains and l in c2.contains
    all l: living | l in container.contains
  }

pred p{}
//run p for exactly 4 living, exactly 2 end, exactly 1 boat

check {
   all c:container | person not in c.contains implies 
    not (lion in c.contains and 
     sheep in c.contains)
     
} for exactly 4 living, exactly 2 end,exactly  1 boat 
