open util/ordering[train1]
open util/ordering[train2]

abstract sig train
{
tr:one Int,
sno:one Int,
state:one Int
}
sig train1,train2 extends train{}

one sig st{seg:one Int}

fact
{
all t:train1|t=first <=> t.tr=1 and t.sno=1 and t.state=1
all t:train2|t=first => t.tr=1 and t.sno=7 and t.state=1
st.seg>1 and st.seg<7

all t:train1|t!=last =>
t.next.state=t.state.add[1]

all t:train2|t!=last =>
t.next.state=t.state.add[1]
}

pred p{}
run p for exactly 10 train1,exactly 10 train2,5 int
//******************************************************
fact
{
all t:train1|t!=last and
t.tr=1 and t.sno < st.seg.sub[1] =>
up[t.next,t.sno,1]

all t:train1|t!=last and
t.tr=1 and t.sno >=st.seg =>
up[t.next,t.sno,1]

all t:train2|t!=last and
t.tr=1 and t.sno > st.seg.add[1] =>
down[t.next,t.sno,1]

all t:train2|t!=last and
t.tr=1 and t.sno <=st.seg =>
down[t.next,t.sno,1]
}
//*****************************************************
pred up[t:train1,s:Int,tk:Int]
{
t.sno=s.add[1] and
t.tr=tk
}

pred down[t:train2,s:Int,tk:Int]
{
t.sno=s.sub[1] and
t.tr=tk
}
//*****************************************************
fact
{
all t:train1,t2:train2|t!=last and t2!=last and
t.sno=st.seg.sub[1] and t2.sno > st.seg.add[1] =>
up[t.next,t.sno,2]

all t:train2,t1:train1|t!=last and t1!=last and
t.sno=st.seg.add[1] and t1.sno < st.seg.sub[1] =>
down[t.next,t.sno,2]
}
