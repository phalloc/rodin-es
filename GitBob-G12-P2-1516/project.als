//Specification of Software
//GitBib Project - Group 12 - 2015/2016

//GITBOB
one sig GitBob{
 users: set Reg_User
}{
 no disj u1,u2 : users | u1 = u2
}

//REG_USERS
sig Reg_User{
id: one User,
type:  one Utypes,
email : one Uemails
}
// -------------------------------------- //

//USERS
sig User{}
// ---------------------------------------- //

//TYPES
abstract sig Utypes{}
one sig Basic, Premium extends Utypes{}
// -------------------------------------- //

//EMAILS
sig Uemails {}
// ------------------------------------- //

//FILES
//sig Files {}
// ------------------------------------  //

//MODES
abstract sig Modes {}
sig Regular, Securely, Readonly extends Modes{}
// ------------------------------------- //

//FUNCTION newUser
pred newUser [gb, gb' : GitBob, usr:User, newtype:Utypes, newemail:Uemails] {
 no u:gb.users | u.id = usr
 gb'.users = gb.users + { user:Reg_User | user.id = usr && user.type = newtype && user.email = newemail} 
}

//FUNCTION removeUser
pred removeUser [gb, gb' : GitBob, usr:User]{
	gb'.users = gb.users - { user:Reg_User | user.id = usr}
}

//FUNCTION upgradePremium
pred upgradePremium [gb, gb' : GitBob, usr:User]{
     some u,u':Reg_User | u.id = usr and u.type = Basic and u'.type = Premium 
}

//FUNCTION downgradeBasic
pred downgradeBasic [gb, gb' : GitBob, usr:User]{
	some u,u':Reg_User | u.id = usr and u.type = Premium and u'.type = Basic
} 
	
//RESTRICTION 1

//RESTRICTION 2

//RESTRICTION 3
fact unique_emails {
 all disj e1,e2 : Reg_User.email | e1 != e2 
}

//RESTRICTION 4
pred init [gb : GitBob] { no gb.users }

pred show {}
run init
run newUser for  10 User, 10 Reg_User, 10 Uemails, 0 Modes
//run upgradePremium
//run downgradeBasic 




