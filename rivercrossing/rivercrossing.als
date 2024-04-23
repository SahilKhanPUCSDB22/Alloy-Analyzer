open util/ordering[village]

sig village
{
bank1:set char,
bank2:set char
}

abstract sig char{}
one sig man,goat,grass,lion extends char{}

fact
{
first.bank1=char

no v:village|
some v.bank1&v.bank2

all v:village|
lion+goat in v.bank1 => man in v.bank1

all v:village|
grass+goat in v.bank1 => man in v.bank1

all v:village|
lion+goat in v.bank2 => man in v.bank2

all v:village|
grass+goat in v.bank2 => man in v.bank2
}

fact
{
all v:village|v!=last and man in v.bank1 =>
one x:v.bank1| v.next.bank2=v.bank2+man+x and 
v.next.bank1=v.bank1-man-x

all v:village|v!=last and man in v.bank2 =>
one x:v.bank2|v.next.bank1=v.bank1+man+x and
v.next.bank2=v.bank2-man-x
}

pred p{last.bank2=char}

run p for exactly 10 village,4 char
