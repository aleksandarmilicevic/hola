/**
 * A model of grade assignment policy
 * Demonstrates automated synthesis of policies in Alloy*
 * Based on the running example from the paper
 *   "Verification and change-impact analysis of access-control policies" by
 * 	 Kathi Fisler, Shriram Krishnamurthi, Leo A. Meyerovich, Michael Carl Tschantz, ICSE 2005.
 */
module GradePolicy

--------------------------------------------------------------------------------
-- Basic signatures
--------------------------------------------------------------------------------

abstract sig Resource {}
abstract sig Action {}
abstract sig Role {}
sig User {}

--------------------------------------------------------------------------------
-- Domain-specific signatures
--------------------------------------------------------------------------------

one sig Faculty, Student, TA extends Role {}
one sig IntGrade, ExtGrade   extends Resource {}
one sig Assign, Receive      extends Action {}

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

/* no student can assign external grade */
pred prop1[roles : User->Role, performs : User->Action->Resource] {
  no u: User | u.roles = Student and Assign->ExtGrade in u.performs
}

/* no user can both receive and assign external grades */
pred prop2[roles : User->Role, performs : User->Action->Resource] {
  no u: User | Assign + Receive in u.performs.ExtGrade
}

/* ’performs’ describes the behavior of users */
pred enforce[acl:      Role->Action->Resource,
             roles:    User->Role,
             performs: User->Action->Resource] {
  all u: User, a: Action, r: Resource |
  /* ’u’ can perform ’a’ on ’r’ only if allowed by ’acl’ */
  u->a->r in performs => (some ro: u.roles | ro->a->r in acl)
}

/* Assumption: no user can both be a faculty and a student/TA */
pred noDualRoles[roles : User->Role] {
  no u: User | Faculty in u.roles and some (Student + TA) & u.roles
}

--------------------------------------------------------------------------------
-- Synthesis predicates
--------------------------------------------------------------------------------

/* ’acl’ satisfies properties over every user role and behavior */
pred valid[acl: Role->Action->Resource] {
  all roles: User->Role, performs : User->Action->Resource |
    (enforce[acl, roles, performs] and noDualRoles[roles]) implies
      (prop1[roles, performs] and prop2[roles, performs])
}

/* ’acl’ allows the most number of actions while being valid */
pred mostPermissive[acl: Role->Action->Resource] {
  valid[acl]
  no acl': Role->Action->Resource |
    acl != acl' and valid[acl'] and #acl' > #acl
}

--------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------

run valid for 4 but 6 Int		-- synthesize a valid policy
run mostPermissive for 4 but 6 Int	-- synthesize the most permissive valid policy
