{
	num_words=split($0,words," ")
	if(length(words)==1){
		gsub("\""," ",$0);
		print "insert into "$1" values('"$1"');"
	}
	gsub("<tuple>","",$0);
	gsub("</tuple>","",$0);
	gsub("<atom label=","",$0);
	gsub("/>","",$0)

	if(length(words)!=1){
		print "update table "$1" set "$2" 
	}

}
