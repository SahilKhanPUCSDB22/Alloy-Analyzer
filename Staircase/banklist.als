sig bank
{
nb: lone bank,
has: set acnt,
bno: one Int
}
{
#has=2
}
sig acnt
{
na : lone acnt
}

fact
{
//ordering on bank
all b:bank|
some b.nb <=> b.nb.bno=b.bno.add[1]

//no cycle bank
no b:bank|
b in b.nb

//list property bank
one b:bank |
b not in b.^nb and (bank-b) in b.^nb and b.bno=1

//last ele in list
one b:bank|
no b.nb

//no intersection bank
no b:bank|
some b.has&(bank-b).has

//no intersection account
no a:acnt|
some a.na&(acnt-a).na

//last bank
all b:bank|
no b.nb <=> no b.has.na

no b:bank|
(acnt+acnt.na) in b.has

no a:acnt|
a in a.na

all b:bank,a:acnt|
some b.nb and
b.has=a <=> b.nb.has=a.na
}

pred p{}

run p for exactly 3 bank , 6 acnt
