//Specification of Software
//GitBib Project - Group 12 - 2015/2016

open util/ordering[GitBob]

//GITBOB
sig GitBob{
	users: set Reg_User,
	files: set Reg_File
}

//USERS

sig User{}

sig Reg_User{
	id: one User,
	type:  one Utypes,
	email : one Uemails
}
 
// ---------------------------------------- //

//TYPES
abstract sig Utypes{}
one sig Basic, Premium extends Utypes{}
// -------------------------------------- //

//EMAILS
sig Uemails {}
// ------------------------------------- //

//FILES

sig File{}

sig Reg_File {
	id: File,
	size: Int,
	version: Int,
	owner: Reg_User
//access: set Reg_User
}
// ------------------------------------  //

//MODES
abstract sig Modes {}
sig Regular, Securely, Readonly extends Modes{}
// ------------------------------------- //

//FUNCTION newUser
pred newUser [gb, gb' : GitBob, usr:Reg_User] {
	no u : gb.users | u.id = usr.id or u.email = usr.email
	gb'.users = gb.users + usr
 	gb'.files = gb.files 
}

//FUNCTION removeUser
pred removeUser [gb, gb' : GitBob, usr:User]{
	gb'.users = gb.users - { user:Reg_User | user.id = usr}
     gb'.files = gb.files
}

//FUNCTION upgradePremium
pred upgradePremium [gb, gb' : GitBob, usr:User]{
     some u,u':Reg_User | u.id = usr.id and u.type = Basic and u'.type = Premium
     gb'.files = gb.files 
}

//FUNCTION downgradeBasic
pred downgradeBasic [gb, gb' : GitBob, usr:User]{
	some u,u':Reg_User | u.id = usr.id and u.type = Premium and u'.type = Basic
    gb'.files = gb.files
}

//FUNCTION addFile
pred addFile[gb, gb' : GitBob, f:File, s:Int, own:Reg_User]{
    gb'.files = gb.files + { file:Reg_File | file.id = f and file.size = s and file.version = 1 and file.owner = own}
    gb'.users = gb.users
}

//FUNCTION removeFile
pred removeFile[gb, gb' : GitBob, f:File, u:Reg_User]{
   gb'.files = gb.files - {file:gb.files | file.id = f and file.owner = u}
   gb'.users = gb.users
}

//FUNCTION uploadFile
pred uploadFile[gb, gb' : GitBob, file:File, u:Reg_User]{
   some f,f':gb.files | f.id = file and f.owner = u and f'.version = f.version +1
   gb'.users = gb.users
}

//FUNCTION downloadFile
pred downloadFile[gb, gb' : GitBob, file:File, u:Reg_User]{
   some f:gb.files | f.id = file and f.owner = u
   gb'.users = gb.users
}




 
	
//RESTRICTION 3
//fact unique_emails {
// all disj e1,e2 : Reg_User | e1.email != e2.email 
//}


/*
fact bam{
 all gb: GitBob | #gb.users >= 1
}*/

fact traces{
 all gb: GitBob - last | let gb' = gb.next |
 	some u:User, f:File, s:Int, ru:Reg_User |
   		newUser[gb,gb',ru] or
   		removeUser[gb, gb', u] or
   		upgradePremium[gb, gb', u] or
   		downgradeBasic[gb, gb', u] or
         addFile[gb, gb', f, s, ru] or
         removeFile[gb, gb', f, ru]
}


//RESTRICTION 4
pred init [gb : GitBob] { no gb.users }

pred show {}
run init
run newUser for 5 but 0 Modes, 4 GitBob
//run removeUser for 1 but 0 Modes
//run upgradePremium
//run downgradeBasic
//run addFile for 3 but 0 Modes
//run removeFile for 10 but 0 Modes
//run uploadFile for 3 but 0 Modes 




