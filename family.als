sig person{
mother : lone person ,
father : lone person ,
sibling : set person
}
pred show{ 
no x : person | x in x.^sibling 
no x: person | x in x.^father 
no x :person | x in x.^mother
}
run show for 50
