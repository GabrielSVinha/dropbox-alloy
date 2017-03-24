open SAObject as SAObject
open File as File
open Folder as Folder

one sig Dropbox {
	// represents the fully set of Dropbox's objects
	scope: set SAObject,
	// the root folder that is in the scope
	root: Folder & scope,
	// the set of parents mapped as (dropbox, object, parent)
	// it's limited to only one parent (except the root, with no parent), that is in the scope
	parent: (scope - root) -> one (Folder & scope),
	// the set of contents of each folder, mapped as (dropbox, folder, object)
	contents : Folder -> SAObject
}{
	// ensure that the set of objects is all objects into the contents and the root
	scope in root.*contents
	parent = ~contents
}

// --------------- FACTS --------------- //

// ensure that all objects is in at least one and exactly one dropbox
fact {
	all obj: SAObject | one db: Dropbox | obj in getAllObjects[db]
}

// --------------- FUNCTIONS --------------- //

// gets the parent of a object in a dropbox
fun getParent[db: Dropbox, o: SAObject]: one Folder {
	o.(db.parent)
}

// gets all objects of the dropbox
fun getAllObjects[db: Dropbox]: set SAObject {
	db.scope
}

// gets the contents of a folder
fun getContents[db: Dropbox, f: Folder]: set SAObject {
	f.(db.contents)
}

// --------------- PREDICATES --------------- //

pred move [dbI, dbF: Dropbox, obj: SAObject, folder: Folder] {
	(obj + folder) in getAllObjects[dbI]
	dbF.parent = dbI.parent - obj->(getParent[dbI, obj]) + obj->folder
}

pred remove [dbI, dbF: Dropbox, obj: SAObject] {
	obj in (getAllObjects[dbI] - dbI.root)
	dbF.parent = dbI.parent - obj->((getParent[dbI, obj]))
}

pred add [dbI, dbF: Dropbox, obj: SAObject, folder: Folder] {
	folder in getAllObjects[dbI]
	dbF.parent = dbI.parent + obj->folder
}

// --------------- ASSERTS --------------- //

// assert that there is only one root in a dropbox
assert oneRoot {
	one f: Folder | one db: Dropbox | no getParent[db, f]
}

// assert that a folder is not in its contents
assert acyclic {
	no f: Folder, db: Dropbox | f in getContents[db, f] // algo errado
}

// assert that all objects has one location in the dropbox
assert oneLocation {
	all obj: SAObject | lone f: Folder | one db: Dropbox | obj in getContents[db, f]
}

assert moveOk {
	all dbI, dbF: Dropbox, obj: SAObject, folder: Folder |
		move[dbI, dbF, obj, folder] => getAllObjects[dbF] = getAllObjects[dbI]
}

assert removeOk {
	all dbI, dbF: Dropbox, obj: SAObject |
		remove[dbI, dbF, obj] => getAllObjects[dbF] = getAllObjects[dbI] - obj
}

assert addOk {
	all dbI, dbF: Dropbox, obj: SAObject, folder: Folder |
		add[dbI, dbF, obj, folder] => getAllObjects[dbF] = getAllObjects[dbI] + obj
}

// --------------- CHECK --------------- //

check oneRoot for exactly 10 SAObject
check acyclic for exactly 10 SAObject
check oneLocation for exactly 10 SAObject
check moveOk for 10
check removeOk for 10
check addOk for 10

// --------------- EXECUTION --------------- //

pred show [] {
}

run show for exactly 10 SAObject
