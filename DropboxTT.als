module Dropcaixa
open util/ordering[Time]

// --------------- SIGS --------------- //
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
	backup: Backup -> Time
}

sig  Backup{}
sig Info{}

// --------------- FACTS --------------- //
// Toda pasta é pai dos seus filhos
fact {
	all o: Folder|getFolderContents[o].parent = o
}

//Nao existe pasta dentro de si mesma ou de seus filhos
fact {
	no o: Folder| o in o.^contents
}

//Todos as pastas estão dentro de root
fact {
	all o: Folder| o !in getDropboxContents[] implies o in getDropboxContents[].^contents
}

//Nao existe pasta que é pai de si mesma
fact {
	no o: Object| o.parent = o
}

//Dropbox é pai dos seus filhos
fact {
	all d: Dropbox| getDropboxContents[].parent = d
}

//Toda info é diferente
fact {
		all i: Info| one i.~info
}

//Se o pai é o dropbox, que ele esteja entre seus filhos
fact{
	all f:Object| (f.parent = Dropbox) => f in getDropboxContents[]
}

//Logica Temporal
fact traces{
	init[first]
	security[first]

	all t: Time, f: File, b: Backup|
		addBackup[f,b,t] or removeBackup[f,b,t]
}
	
// --------------- PREDS --------------- //
pred init[t: Time]{
	no Device.dropbox.t
}

pred security[t: Time]{
		all t': t.nexts |
			Device.dropbox.t' = Dropbox
}

pred addBackup[f: File, b: Backup, t: Time]{
	#(getBackup[f]) < 0
	all x : t.nexts |
		f.backup.x = b
}

pred removeBackup[f: File, b: Backup, t: Time]{
	#(getBackup[f]) > 0
	all x : t.nexts|
	b !in f.backup.x

}


// --------------- FUNCS --------------- //
fun getFolderContents[f: Folder]: set Object{
	f.contents
}


fun getDropboxContents[]: set Object{
	Dropbox.contents
}

fun getBackup[f: File]: set Backup -> Time{
	f.backup
}

// --------------- ASSERTS --------------- //
//Todas as pastas dentro de Dropbox
assert folderInDropbox {
	all f: Folder | f !in Dropbox.contents implies f in Dropbox.contents.^contents
}

//Todos os arquivos dentro de Dropbox
assert  fileInDropbox{
	all f: File | f !in Dropbox.contents implies f in Dropbox.contents.^contents
}

// unathorized in the beggining
assert security{
	#Device.dropbox.first = 0
}

//check folderInDropbox
//check fileInDropbox
//check security

pred show[]{}

run show for 10 but 5 Time
