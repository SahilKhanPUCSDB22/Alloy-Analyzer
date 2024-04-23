open util/ordering[bank]

sig bank
{
has : set account
}
{
#has=4
}

fact
{
no b1,b2:bank|
b1!=b2 and some b1.has&b2.has

no a1,a2:account|
a1!=a2 and some a1.nextb&a2.nextb

all b:bank|
b!=last <=> some b.has.nextb

all b:bank|
b=first <=> b.has not in account.^nextb

no a:account|
a in a.nextb
}

check
{
all b:bank|
b=last => no b.has.nextb
}

sig account
{
balance : one Int,
nextb: lone account
}

pred p{}

run p for exactly 3 bank , exactly 12 account , 5 int 
