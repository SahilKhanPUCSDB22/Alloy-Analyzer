open util/ordering[el] 

fact
{
first.ind=1
}

sig el
{
ind:one Int
}

fact
{
all e:el , en:e.next , i:Int|
e.ind=i => inc[en,i]
}

//pred dec[en:set el , i:set Int]
//{
//i>1 => en.ind=i.sub[1]
//else 
//en.ind=i
//}

pred inc[en:set el , i: set Int]
{
i<5 =>en.ind=i.add[1]
else
en.ind=i
}

pred p{}
run {last.ind=5} for exactly 10 el
