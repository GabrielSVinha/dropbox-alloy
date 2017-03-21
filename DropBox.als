open SAObject as SAObject
open File as File
open Folder as Folder

one sig Dropbox extends SAObject{
contents : set SAObject
}{no parent}

//fact DropboxRoot {all f: Folder, d: Dropbox | f.contents != d}

//Drop não esta nele mesma
fact {
	all d: Dropbox |d !in d.contents
}
//Drop nao pode estar vazio
fact{
	all d:Dropbox |#(d.contents) > 0
}

pred show[] {}
run show for 5
