module GradePolicy

abstract sig Role {}
abstract sig Resource {}
abstract sig Action {}

sig User {
	roles : set Role,
}

one sig Faculty, Student extends Role {}
sig InternalGrade, ExternalGrade extends Resource {}
one sig Assign, View, Receive extends Action {}

sig Policy {
	allowed : Role -> Action -> Resource
}
pred applyPolicy[p : Policy, performs : User -> Action -> Resource] {
	all u : User, a : Action, r : Resource |
		a -> r in u.performs implies
			some ro : u.roles |
				ro -> a -> r in p.allowed
}

pred studentsCantAssignExGrades[performs: User -> Action->Resource] {
	-- "there do not exist members of Student who can Assign ExternalGrade
	no u : User {
		Student in u.roles
		 some eg : ExternalGrade | Assign -> eg in u.performs
	}
}

pred facultyCanAssignAllGrades[performs : User -> Action -> Resource] {
	-- "Faculty can"
	all g : InternalGrade + ExternalGrade | Faculty -> Assign -> g in performs
}

pred noBadCombo[performs : User -> Action -> Resource] {
	-- "no combination of roles exist such that a user with those roles can both Receive and Assign ExternalGrades
	no u : User | Assign + Receive in u.performs.ExternalGrade
}
fact {
	some roles.Faculty
//	no roles.Faculty & roles.Student
}
run {
	some p : Policy | all performs: User -> Action->Resource |
		applyPolicy[p, performs] implies
			(studentsCantAssignExGrades[performs] and
			facultyCanAssignAllGrades[performs] and
			noBadCombo[performs])
} for 7

