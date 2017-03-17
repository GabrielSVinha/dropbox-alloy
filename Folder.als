open SAObject as SAObject
open File as File

sig Folder extends SAObject{
	contents: set SAObject
}

fact invariables{
	all f: Folder | f !in f.contents
}

pred show[] {}

run show for 5
