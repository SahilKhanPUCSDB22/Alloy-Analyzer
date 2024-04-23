open util/ordering[st1]
open util/ordering[st2]

sig st1{
s1 : one Int,
link:one Int
}

sig st2{
s2 : one Int,
link:one Int
}

fact
{
all s:st1,i:Int|
s!=last and
s.link=i =>s.next.link=i.add[1]

all s:st2,i:Int|
s!=last and
s.link=i =>s.next.link=i.add[1]

all s:st1|s=first <=> s.link=1

all s:st2|s=first <=> s.link=1
}

fact
{
first.s1=10 and first.s2=1
}

fact
{
all s:st1|
s!=last and s.s1 > 1 =>
s.next.s1=s.s1.sub[1] or s.next.s1=s.s1.sub[2]

no s:st1|s!=last and
s.s1 < 1

no s:st2|s!=last and
s.s2 > 10

all s:st1|
s!=last and s.s1=1 => s.next.s1=s.s1

all s:st2|
s!=last and s.s2=10 => s.next.s2=s.s2

all s:st2|
s!=last and s.s2 < 10 =>
s.next.s2=s.s2.add[1] or s.next.s2=s.s2.add[2]

no sa:st1,sb:st2|
sa.link=sb.link and sa.s1=sb.s2
}

pred r
{
some sa:st1,sb:st2|
sa.s1=sb.s2 and sa.link=sb.link
}

pred p{last.s1=1 and last.s2=10}

run p for 6 but 5 int

run r for 10 but 5 int
