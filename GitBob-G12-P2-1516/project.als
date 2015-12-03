//Specification of Software
//GitBib Project - Group 12 - 2015/2016

//allow state
open util/ordering[GitBob]
open util/ordering[Reg_User]


//data structures
abstract sig Utypes{}
one sig Basic, Premium extends Utypes{}

abstract sig Modes {}
one sig Regular, Securely, Readonly extends Modes{}

sig Uemails{}

sig User{}
sig Reg_User{
	id: one User,
	type:  one Utypes,
	email : one Uemails
} // restriction 2

sig File{}
sig Reg_File {
	id: File,
	size: Int,
	version: Int,
	owner: one Reg_User
}

sig GitBob{
	users: set Reg_User,
	files: set Reg_File,
   shares: users -> files
}{
	all disj u1,u2: users | u1.email != u2.email or u1.id != u2.id // restriction 3
}


//functions
pred newUser [gb, gb' : GitBob, usr:Reg_User] { // restriction 1
	no u : gb.users | u.id = usr.id or u.email = usr.email // restriction 5
	gb'.users = gb.users + usr
 	gb'.files = gb.files 
}

pred removeUser [gb, gb' : GitBob, usr:Reg_User]{ // restriction 6
	gb'.users = gb.users - { user:Reg_User | user = usr}
	gb'.files = gb.files
}

pred upgradePremium [gb, gb' : GitBob, usr:Reg_User]{ // restriction 7,9
     some u,u':Reg_User | u = usr
                                        and u.type = Basic
											 and u'.type = Premium 
											 and u'.email = u.email
											 and u'.id = u.id
											 and gb'.users = gb.users - u + u'
     gb'.files = gb.files 
}

pred downgradeBasic [gb, gb' : GitBob, usr:Reg_User]{
	some u,u':Reg_User | u = usr and u.type = Premium and u'.type = Basic // restriction 8,9
    gb'.files = gb.files
}

pred addFile[gb, gb' : GitBob, f:File, s:Int, own:Reg_User]{
    gb'.files = gb.files + { file:Reg_File | file.id = f and file.size = s and file.version = 1 and file.owner = own}
    gb'.users = gb.users
}

pred removeFile[gb, gb' : GitBob, f:File, u:Reg_User]{
   gb'.files = gb.files - {file:gb.files | file.id = f and file.owner = u}
   gb'.users = gb.users
}

pred uploadFile[gb, gb' : GitBob, file:File, u:Reg_User]{
   some f,f':gb.files | f.id = file and f.owner = u and f'.version = f.version +1
   gb'.users = gb.users
}

pred downloadFile[gb, gb' : GitBob, file:File, u:Reg_User]{
   some f:gb.files | f.id = file and f.owner = u
   gb'.users = gb.users
}


//predicates
pred init [gb : GitBob] { // restriction 4
  no gb.users
  no gb.files
  no gb.shares
}

//assure only our functions can change state
fact traces{
 all gb: GitBob - last | let gb' = gb.next |
 	some ru:Reg_User, f:File, s:Int |
   		newUser[gb,gb',ru] or
   		removeUser[gb, gb', ru] or
   		upgradePremium[gb, gb', ru] 
   		//downgradeBasic[gb, gb', ru] or
       //addFile[gb, gb', f, s, ru] or
       //removeFile[gb, gb', f, ru]
}

pred torun[usr1, usr2, usr3:Reg_User]{
init[first]
newUser[first, first.next, usr1]
upgradePremium[first.next, first.next.next , usr1]
newUser[first.next.next, first.next.next.next, usr2]
//upgradePremium[g''',g'''',usr1]
}

pred show {}
run init
run torun for 5 but 0 Modes
//run removeUser for 1 but 0 Modes
//run upgradePremium
//run downgradeBasic
//run addFile for 3 but 0 Modes
//run removeFile for 10 but 0 Modes
//run uploadFile for 3 but 0 Modes 


/*
fact bam{
 all gb: GitBob | #gb.users >= 1
}*/
 




