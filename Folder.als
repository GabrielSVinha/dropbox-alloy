open SAObject as SAObject
open File as File
sig Folder extends SAObject{
	contents: set (Folder + File)
}

//Uma pasta não pode se conter
fact {
	all f: Folder | f !in f.contents
}

//Uma pasta é pai das suas pastas filhas
fact {
	all f: Folder| f.contents.parent = f 
}

//Uma pasta nao pode conter seu pai
fact {
	all f: Folder| f.contents != f.parent
}
