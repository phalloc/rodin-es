//Specification of Software
//GitBib Project - Group 12 - 2015/2016

abstract sig users{
reg : set reg_users
}

sig reg_users extends users{
type : utypes
}

sig utypes{}
check {}


