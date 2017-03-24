open SAObject as SAObject
open File as File
open Folder as Folder

one sig Dropbox {
	live: set SAObject,
	root: Folder & live,
	parent: (live - root) -> one (Folder & live),
	contents : Folder -> SAObject
}{
	live in root.*contents
	parent = ~contents
}

pred show {
}

run show for exactly 10 SAObject
