open util/ordering[st1]
open util/ordering[st2]
//******************************************************
fact
{
all s:st1|s!=last
and s.s1=1 and 
s.ac=dec => 
s.next.s1=s.s1 and s.next.pac=dec

all s:st1|s!=last 
and s.s1=1 and
s.ac=inc =>
s.next.s1=s.s1.add[1] or s.next.s1=s.s1.add[1] and
s.next.pac=inc

all s:st1|s!=last
and s.s1=10 and s.ac=dec => 
s.next.s1=s.s1.sub[1] or s.next.s1=s.s1.sub[1]
and s.next.pac=dec

all s:st1|s!=last 
and s.s1=10 and
s.ac=inc =>
s.next.s1=s.s1 and
s.next.pac=inc

all s:st1|s!=last
and s.s1 >=3 and s.s1<=8
and s.ac=inc and s.pac=inc =>
s.next.pac=inc and s.next.s1=s.s1.add[1] or
s.next.s1=s.s1.add[2]

all s:st1|s!=last
and s.s1>=3 and s.s1<=8 and
s.pac!=s.ac => 
s.next.s1=s.s1 and
s.next.pac=s.pac

all s:st1|s!=last
and s.s1=9 and s.pac=inc and s.ac=inc =>
s.next.s1=s.s1.add[1] and s.next.pac=inc

all s:st1|s!=last
and s.s1=9 and s.pac=inc and s.ac=dec =>
s.next.pac=s.pac and s.next.s1=s.s1

all s:st1|s!=last
and s.s1=9 and s.pac=dec and s.ac=dec =>
(s.next.s1=s.s1.sub[1] or s.next.s1=s.s1.sub[2]) 
and s.next.pac=dec

all s:st1|s!=last
and s.s1=9 and s.pac=dec and s.ac=inc =>
s.next.pac=s.pac and s.next.s1=s.s1

all s:st1|s!=last
and s.s1 >=3 and s.s1<=8
and s.ac=dec and s.pac=dec =>
s.next.pac=dec and 
s.next.s1=s.s1.sub[1] or
s.next.s1=s.s1.sub[2]

all s:st1|s!=last
and s.s1=2 and s.pac=inc and s.ac=inc =>
s.next.s1=s.s1.add[1] or s.next.s1=s.s1.add[2]
and s.next.pac=inc

all s:st1|s!=last
and s.s1=2 and s.pac=inc and s.ac=dec =>
s.next.pac=s.pac and s.next.s1=s.s1

all s:st1|s!=last
and s.s1=2 and s.pac=dec and s.ac=dec =>
s.next.s1=s.s1.sub[1] 
and s.next.pac=dec

all s:st1|s!=last
and s.s1=2 and s.pac=dec and s.ac=inc =>
s.next.pac=s.pac and s.next.s1=s.s1
}
//******************************************************
sig st1{
s1 : one Int,
ac : one act,
pac: one act,
link:one st2,
ind1:one Int
}

sig st2{
s2 : one Int,
ac : one act,
pac: one act,
link:one st1,
ind2:one Int
}

abstract sig act{}
one sig inc,dec extends act{}

fact
{
all s:st1,i:Int|
s!=last and
s.ind1=i =>s.next.ind1=i.add[1]


all s:st2,i:Int|
s!=last and
s.ind2=i =>s.next.ind2=i.add[1]
}

fact
{
first.s1=1 and first.s2=10 or
first.s2=1 and first.s1=10

first.ind1=1 and first.ind2=1
}

fact
{
no sa,sb:st1|sa!=sb and 
some sa.link&sb.link

no sa,sb:st2|sa!=sb and 
some sa.link&sb.link

all sa:st1,sb:st2|
sa.ind1=sb.ind2 <=> sa.link=sb and sb.link=sa
}

pred p{last.s1=9 and last.s2=9}
run p for exactly 12 st1 ,  exactly 12 st2 , 7 int

//****************************************************
fact
{
all s:st2|s!=last
and s.s2=1 and 
s.ac=dec => s.next.s2=s.s2 and s.next.pac=s.ac

all s:st2|s!=last 
and s.s2=1 and
s.ac=inc =>
s.next.s2=s.s2.add[1] or s.next.s2=s.s2.add[1] and
s.next.pac=inc

all s:st2|s!=last
and s.s2=10 and 
s.ac=dec => 
s.next.s2=s.s2.sub[1] or s.next.s2=s.s2.sub[1]
and s.next.pac=s.ac

all s:st2|s!=last 
and s.s2=10 and
s.ac=inc =>
s.next.s2=s.s2 and
s.next.pac=inc

all s:st2|s!=last
and s.s2 >=3 and s.s2<=8
and s.ac=inc and s.pac=inc =>
s.next.pac=inc and s.next.s2=s.s2.add[1] or
s.next.s2=s.s2.add[2]

all s:st2|s!=last
and s.s2>=3 and s.s2<=8 and
s.pac!=s.ac => s.next.s2=s.s2 and
s.next.pac=s.pac

all s:st2|s!=last
and s.s2=9 and s.pac=inc and s.ac=inc =>
s.next.s2=s.s2.add[1] and s.next.pac=s.pac

all s:st2|s!=last
and s.s2=9 and s.pac=inc and s.ac=dec =>
s.next.pac=s.pac and s.next.s2=s.s2

all s:st2|s!=last
and s.s2=9 and s.pac=dec and s.ac=dec =>
s.next.s2=s.s2.sub[1] or s.next.s2=s.s2.sub[2] 
and s.next.pac=s.pac

all s:st2|s!=last
and s.s2=9 and s.pac=dec and s.ac=inc =>
s.next.pac=s.pac and s.next.s2=s.s2

all s:st2|s!=last
and s.s2 >=3 and s.s2<=8
and s.ac=dec and s.pac=dec =>
s.next.pac=dec and s.next.s2=s.s2.sub[1] or
s.next.s2=s.s2.sub[2]

all s:st2|s!=last
and s.s2=2 and s.pac=inc and s.ac=inc =>
s.next.s2=s.s2.add[1] or s.next.s2=s.s2.add[2]
and s.next.pac=s.pac

all s:st2|s!=last
and s.s2=2 and s.pac=inc and s.ac=dec =>
s.next.pac=s.pac and s.next.s2=s.s2

all s:st2|s!=last
and s.s2=2 and s.pac=dec and s.ac=dec =>
s.next.s2=s.s2.sub[1] 
and s.next.pac=s.pac

all s:st2|s!=last
and s.s2=2 and s.pac=dec and s.ac=inc =>
s.next.pac=s.pac and s.next.s2=s.s2
}
//****************************************************** 
