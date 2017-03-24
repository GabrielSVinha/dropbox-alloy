sig FSObject {
	parent: lone Dir
}

sig Dir extends FSObject{
	contents: set  FSObject
}

sig File extends FSObject{
}

one sig Root extends Dir{}{
	no parent
}

fact connection{
	FSObject in Root.*contents
}

fact parentRule{
	all dir: Dir, obj: dir.contents | obj.parent = dir
}

fact {
	File + Dir = FSObject
}

assert oneRoot{
	one dir: Dir | no dir.parent
}

assert acyclicsm{
	no dir: Dir | no dir.parent
}

check acyclicsm for 4

//check oneRoot for 4

pred show[]{}

run show for 4
