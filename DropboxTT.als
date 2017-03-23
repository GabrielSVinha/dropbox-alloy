module Dropcaixa
open util/ordering[Time]

sig Time{}

one sig Device{
	dropbox: Dropbox -> Time
}

one sig Dropbox{
	contents: some (Folder + File)
}

abstract sig Object{
	parent: one (Object - File + Dropbox)
}

sig Folder extends Object{
	contents: set Object
}

sig File extends Object{
	info : one Info,
	backup: one Backup
}

sig  Backup{}
sig Info{}

// Toda pasta é pai dos seus filhos
fact {
	all o: Folder| o.(contents).parent = o
}

//Nao existe pasta dentro de si mesma ou de seus filhos
fact {
	no o: Folder| o in o.^contents
}
//Nao existe pasta que é pai de si mesma
fact {
	no o: Object| o.parent = o
}

//Dropbox é pai dos seus filhos
fact {
	all d: Dropbox| d.(contents).parent = d
}

//Toda info é diferente
fact {
		all i: Info| one i.~info
}

//Todo backup é diferent
fact{
	all b: Backup|one b.~backup
}

//Se o pai é o dropbox, que ele esteja entre seus filhos
fact{
	all f:Object| (f.parent = Dropbox) => f in Dropbox.contents
}


pred show[]{}

run show for 10 but 15 Time
