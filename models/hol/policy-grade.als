module GradePolicy

abstract sig Role {}
abstract sig Resource {}
abstract sig Action {}

sig User {}

one sig Faculty, Student extends Role {}
one sig InternalGrade, ExternalGrade extends Resource {}
one sig Assign, View, Receive extends Action {}


pred actionsAllowed[acl: Role->Action->Resource,
                    actions: User->Action->Resource, 
                    roles: User -> Role] {
  all u: User, a: Action, r: Resource |
    u->a->r in actions implies
      some roles[u] -> a -> r & acl
--      a->r in (u.roles).acl
--      (some ro : u.roles | ro -> a -> r in acl)
}

pred studentsCannotAssignExGrades[performs: User -> Action -> Resource, roles: User -> Role] {
  -- "there do not exist members of Student who can assign external grade
  
  no u: User {
    Student in roles[u] 
    Assign -> ExternalGrade in performs[u]
  }
  
  -- the above one seems faster
  --no (roles.Student) -> Assign -> ExternalGrade & performs
}

pred enforcing[acl: Role->Action->Resource] {
  all actions: User->Action->Resource,
      roles: User -> Role |{
    actionsAllowed[acl, actions, roles]
  } |{
    studentsCannotAssignExGrades[actions, roles]
  }
}

pred permissive[acl: Role->Action->Resource] {
  enforcing[acl]
  no acl': Role->Action->Resource {
    acl' != acl
    enforcing[acl']
    acl in acl'
  }
}

run {
  some User
  some p: Role->Action->Resource {
    --Action -> Resource in p[Student]
    --Action -> ExternalGrade in p[Faculty]
    some p 
     permissive[p]
    --enforcing[p]
  }
} for 7
