sig element
{
index : Int ,
value : one data , 
next : one element
}

sig data{}

fact
{
no e1,e2:element , i:Int|
e1!=e2 and
i in e1.index and i in e2.index

/*all e1,e2:element , i1,i2 :Int | e1!=e2 and
i1 in e1.index and i2 in e2.index and
(int i2 > int i1) => e2 in e1.next*/ 
}

pred p{}

run p for exactly 16 element,exactly 16 data , 4 int


