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
run p for exactly 7 train1,exactly 7 train2,5 int
//******************************************************
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
all t1:train1,t2:train2|t1!=last and t2!=last and
t1.tr=1 and t2.tr=1 and
t1.sno < st.seg.sub[1] and
t2.sno > st.seg.add[1] =>
up[t1.next,t1.sno,1] and
down[t2.next,t2.sno,1]
}

fact
{
all t1:train1,t2:train2|t1!=last and t2!=last and
t1.sno =st.seg.sub[1] and t2.sno > st.seg.add[1] =>
up[t1.next,t1.sno,2] and
down[t2.next,t2.sno,1]

all t1:train1,t2:train2|t1!=last and t2!=last and
t2.sno =st.seg.add[1] and t1.sno < st.seg.sub[1] =>
up[t1.next,t1.sno,1] and
down[t2.next,t2.sno,2]
}

fact
{
all t1:train1,t2:train2|t1!=last and t2!=last and
t1.sno=st.seg.sub[1] and t2.tr=2 and t2.sno=st.seg =>
up[t1.next,t1.sno,1] and
down[t2.next,t2.sno,1]

all t1:train1,t2:train2|t1!=last and t2!=last and
t2.sno=st.seg.add[1] and t1.tr=2 and t1.sno=st.seg =>
up[t1.next,t1.sno,1] and
down[t2.next,t2.sno,1]
}

fact
{
all t1:train1,t2:train2|t1!=last and t2!=last and
t1.tr=2 and t1.sno=st.seg and
t2.sno > st.seg.add[1] =>
t1.next.sno=t1.sno and t1.next.tr=t1.tr and
down[t2.next,t2.sno,1]

all t1:train1,t2:train2|t1!=last and t2!=last and
t2.tr=2 and t2.sno=st.seg and
t1.sno < st.seg.sub[1] =>
t2.next.sno=t2.sno and t2.next.tr=t2.tr and
up[t1.next,t1.sno,1]
}


fact
{
all t:train1|t!=last and
t.sno=st.seg and t.tr=1=>
up[t.next,t.sno,1]

all t:train2|t!=last and
t.sno=st.seg and t.tr=1=>
down[t.next,t.sno,1]
}


fact same_to_switch
{
all t1:train1,t2:train2|t1!=last and t2!=last and
t1.sno=st.seg.sub[1] and t2.sno=st.seg.add[1] =>
up[t1.next,t1.sno,2] and down[t2.next,t2.sno,1] or
up[t1.next,t1.sno,1] and down[t2.next,t2.sno,2]
}

fact
{
all t:train1|t!=last and
t.tr=1 and t.sno >st.seg =>
up[t.next,t.sno,1]

all t:train2|t!=last and
t.tr=1 and t.sno <st.seg =>
down[t.next,t.sno,1]
}

fact
{
all t1:train1,t2:train2|t1!=last and t2!=last and
t1.tr=2 and t2.sno=st.seg =>
up[t1.next,t1.sno,1] and
down[t2.next,t1.sno,1]

all t1:train1,t2:train2|t1!=last and t2!=last and
t2.tr=2 and t1.sno=st.seg =>
up[t1.next,t1.sno,1] and
down[t2.next,t1.sno,1]
}
