open util/ordering[track1]
open util/ordering[track2]

fact
{
all t:track1,t1:train1,t2:train2|t1.n=5 and t2.n=1 and
t=first => t.train=(t1+t2) 

all t:track2|t=first => no t.train
}

sig track1
{
train:set train
}

fact
{
all t:track1|#t.train>0 and #t.train<3
all t:track2|t.num>1 and t.num<5
}

sig track2
{
train:lone train,
num:one Int
}

abstract sig train{n:one Int}
{
n>0 and n<6
}
sig train1 extends train{}
sig train2 extends train{}

fact
{
no t:train1|
some t.n&(train1-t).n

no t:train2|
some t.n&(train2-t).n
}

pred p{}
run p for exactly 5 train1 , exactly 5 train2 , exactly 3 
track1, exactly 3 track2 , 5 int

fact
{
all t:track1,t1:train1|t!=last and
t1.n < track2.num.sub[1] => all t2:train1|
t2.n=t1.n.add[1] => t2 in t.next.train

all t:track1,t2:train2|t!=last and
t2.n > track2.num.add[1] => all t1:train2|
t1.n=t2.n.sub[1] => t1 in t.next.train

all t:track1,tt:track2,t1:train1,t2:train2|t!=last and tt!=last and
t1.n=track2.num.sub[1] and t2.n>track2.num.add[1] =>
all x:train1,y:train2|x.n=t1.n.add[1] and y.n=t2.n.sub[1] =>
y in t.next.train and x in tt.next.train


}



