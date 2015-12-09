//Specification of Software
//GitBib Project - Group 12 - 2015/2016

//allow state
open util/ordering[GitBob]
open util/relation

//data structures
abstract sig Utypes{}
one sig Basic, Premium extends Utypes{}

abstract sig Modes {}
one sig Regular, Secure, Readonly extends Modes{}

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
	owner: one Reg_User //restriction 16
} //restriction 10

sig GitBob{
	users: set Reg_User,
	files: set Reg_File, // restriction 37
   shares: files -> users, //restriction 20,21
   modes: files -> Modes //restriction 29
}{
	all disj u1,u2: users | u1.email != u2.email or u1.id != u2.id // restriction 3
} //restriction 12


//functions
pred newUser [gb, gb' : GitBob, usr:Reg_User] { // restriction 1
	no u : gb.users | u.id = usr.id or u.email = usr.email // restriction 5
	gb'.users = gb.users + usr
 	gb'.files = gb.files
   gb'.shares = gb.shares
   gb'.modes = gb.modes 
}

pred removeUser [gb, gb' : GitBob, usr:Reg_User]{ // restriction 6
    no f:gb.files | f.owner = usr // restriction 14
	usr not in ran[gb.shares] // restriction 24
	gb'.users = gb.users - { user:Reg_User | user = usr}
	gb'.files = gb.files
   gb'.shares = gb.shares
   gb'.modes = gb.modes
}

pred upgradePremium [gb, gb' : GitBob, usr:Reg_User]{ // restriction 7,9
     some u,u':Reg_User | u = usr
                                        and u.type = Basic
											 and u'.type = Premium 
											 and u'.email = u.email
											 and u'.id = u.id
											 and gb'.users = gb.users - u + u'
     gb'.files = gb.files
     gb'.shares = gb.shares
     gb'.modes = gb.modes 
}

pred downgradeBasic [gb, gb' : GitBob, usr:Reg_User]{ // restriction 8,9
	some u,u':Reg_User | u = usr 
                                      and u.type = Premium
                                      and u'.type = Basic
										   and u'.email = u.email
										   and u'.id = u.id
                                      //and dom[gb.shares <: usr]  not in dom[gb.modes <: Secure]  //restriction 31
                                      and gb'.users = gb.users - u + u'
    gb'.files = gb.files
    gb'.shares = gb.shares
    gb'.modes = gb.modes
}

pred addFile[gb, gb' : GitBob, f:Reg_File, s:Int, own:Reg_User]{
    no file : gb.files | file = f // restriction 15
    f.size = s and f.version = 1 and f.owner = own //restriction 17
    gb'.files = gb.files + f 
    gb'.shares = gb.shares + f -> own // restriction 22
    gb'.modes = gb.modes + f-> Regular // restriction 32
    gb'.users = gb.users
}

pred removeFile[gb, gb' : GitBob, f:Reg_File, u:Reg_User]{
   some file:gb.files | file = f // restriction 18
   u in gb.shares[f]
   (u = f.owner and gb.modes[f]=Readonly) => gb'.files = gb.files - f else gb'.files=gb.files
   //gb.modes[f]=Readonly and f.owner = u implies gb'.files = gb.files - {file:gb.files | file= f} //restriction 33
   //gb.modes[f] != Readonly implies  gb'.files = gb.files - {file:gb.files | file= f}
   gb'.users = gb.users
   gb'.modes = gb.modes
}

pred uploadFile[gb, gb' : GitBob, file:Reg_File, u:Reg_User]{
   u in gb.shares[file]
   gb.modes[file] = Readonly implies file.owner = u // restriction 34
   some f,f':gb.files | f = file and f'.version = f.version +1 // restriction 18,19
   gb'.users = gb.users
   gb'.shares = gb.shares
}

pred downloadFile[gb, gb' : GitBob, file:Reg_File, u:Reg_User]{
   u in gb.shares[file]
   some f:gb.files | f= file // restriction 18
   gb'.users = gb.users
   gb'.modes = gb.modes
}

pred shareFile[gb,gb' : GitBob, file:Reg_File, u1,u2:Reg_User]{ //restriction 26
   u1 in gb.shares[file]
   u2 in gb.users
   u2 not in gb.shares[file] // restriction 27
   all u : gb.shares[file] | u.type = Premium and gb.modes[file] = Secure and gb'.shares = gb.shares + file -> u2 // restriction 30
   /*all u : gb.shares[file] |*/ gb.modes[file] != Secure and gb'.shares = gb.shares + file -> u2
   gb'.users = gb.users
   gb'.files = gb.files
   gb'.modes = gb.modes
}

pred removeShare[gb,gb' : GitBob, file:Reg_File, u1,u2:Reg_User]{ //restriction 28
   file in gb.files
   u1 in gb.shares[file]
   u2 in gb.shares[file]
   u2 != file.owner
   gb'.shares = gb.shares - file -> u2
   gb'.users = gb.users
   gb'.files = gb.files
   gb'.modes = gb.modes
}

pred changeSharingMode[gb,gb' : GitBob, file:Reg_File, usr:Reg_User, mode:Modes]{
    usr = file.owner //restriction 35
    file in gb.files
    gb'.modes = gb.modes
    /*all u : gb.shares[file] |*/ mode = Readonly and gb'.modes[file] = mode
    /*all u : gb.shares[file] | */mode = Regular and gb'.modes[file] = mode
    all u : gb.shares[file] | u.type = Premium and mode = Secure and gb'.modes[file] = mode //restriction 36
    gb'.users = gb.users
    gb'.files = gb.files
}


//predicates
pred init [gb : GitBob] { // restriction 4,13,23
  no gb.users
  no gb.files
  no gb.shares
}


//assure only our functions can change state
fact traces{
 all gb: GitBob - last | let gb' = gb.next |
 	some user,user2:Reg_User, file:Reg_File, size:Int, mode:Modes |
   		newUser[gb,gb',user] or
   		removeUser[gb, gb', user] or
   		upgradePremium[gb, gb', user] or
   		downgradeBasic[gb, gb', user] or
       addFile[gb, gb', file, size, user] or
       removeFile[gb, gb', file, user] or
       uploadFile[gb, gb', file, user] or
       downloadFile[gb, gb', file, user] or
       shareFile[gb, gb', file, user, user2] or
       removeShare[gb, gb', file, user, user2] or
       changeSharingMode[gb, gb', file, user, mode]  
}

pred torun[usr1, usr2, usr3:Reg_User, file:Reg_File, size:Int, owner:Reg_User]{
init[first]
newUser[first, first.next, usr1]
addFile[first.next, first.next.next, file, size, owner]
removeFile[first.next.next, first.next.next.next, file, owner]
//upgradePremium[first.next, first.next.next , usr1]
//downgradeBasic[first.next.next, first.next.next.next, usr2]
//newUser[first.next.next, first.next.next.next, usr2]
//upgradePremium[g''',g'''',usr1]l
}

pred show {}
run init
run torun for 7 but 0 Modes
//run removeUser for 1 but 0 Modes
//run upgradePremium
//run downgradeBasic
//run addFile for 3 but 0 Modes
//run removeFile for 10 but 0 Modes
//run uploadFile for 3 but 0 Modes 




