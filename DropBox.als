open SAObject as SAObject
open File as File
open Folder as Folder

one sig Dropbox {
	scope: set SAObject,
	root: Folder & scope,
	parent: (scope - root) -> one (Folder & scope),
	contents : Folder -> SAObject
}{
	scope in root.*contents
	parent = ~contents
}

fact {
	all obj: SAObject | one db: Dropbox | obj in db.scope
}

assert oneRoot {
	one f: Folder | one db: Dropbox | no f.(db.parent)
}

assert acyclic {
	no f: Folder, db: Dropbox | f in f.^(db.contents) // algo errado
}

assert oneLocation {
	all obj: SAObject | lone f: Folder | one db: Dropbox | obj in f.(db.contents)
}

pred show {
}

//check oneRoot for exactly 10 SAObject
//check acyclic for exactly 10 SAObject
//check oneLocation for exactly 10 SAObject

run show for exactly 10 SAObject
