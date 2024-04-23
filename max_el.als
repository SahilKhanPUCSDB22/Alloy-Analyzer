one sig list
{
has : some elements
}

sig elements
{
index : disj one Int,
value : one Int,
prop : lone next
}
{
index >-1
}

one sig next{}

check
{
no l:list,e:elements|e in l.has and no e.prop and #e >1
}

one sig max
{
max_el : one elements
}

run
{
#list=1
all e:elements| e in list.has
all l:list|one e:elements| e in l.has and no e.prop
all e:elements,l:list|e in l.has and some e.prop => some e2:elements|
e2!=e and e2.index=e.index.add[1]
all l:list,e:elements|e in l.has and no_bigger_el[e,(l.has-e)] => e in max.max_el
}
for exactly 2 elements

pred no_bigger_el[e,ele:elements]
{
no el:ele| el.value > e.value
}

