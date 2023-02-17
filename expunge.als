-- nathan, ishaq version

-- updates:
-- Expungement for multiple Convictions should work now
-- single fact { } constraints model with many predicates such as 
-- afterFirstTenner and afterSecondAssault 
-- (as opposed to before when we had many individual facts)

-- TODO

-- 1 < Felony (7 yrs), 1 Felony + Misdemeanors (5 yrs), Misdemeanors (3 yrs) (Sec. 1d)
 
-- constrain happens before elegantly
-- libraries of predefined things in alloy
-- orderering.als
-- to do so run the following:
-- open util/ordering[Id]

module expunge

-- An event is a conviction or expungement
abstract sig Event { 
	date: one year
}
abstract sig Conviction extends Event { }
abstract sig Felony extends Conviction { }
abstract sig Misdemeanor extends Conviction { } 
sig OWI in Misdemeanor { }
sig AssaultiveFelony in Felony { }
sig TenYearFelony in Felony { }
sig Expungement extends Event {
	con: some Conviction -- the conviction that is being expunged
}

abstract sig year { 
	happensBefore: set year,
	withinThree: set year
} 

-- Y1, ..., Y4 
one sig Y1, Y2, Y3, Y4 extends year { }

-- Full version, uncomment when very confident in model behavior
--one sig Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10 extends year { }

-- now indicates the current event
var sig now in Event { } 

-- Does the ten-year felony ty occur after a preceding ten-year felony?
pred afterFirstTenner[ty: TenYearFelony] {
	some ty1: TenYearFelony - ty |
		eventually (now = ty1 and (eventually now = ty))
}

-- Does the assaultive felony af occur after two preceding assaultive felonies?
pred afterSecondAssault[af: AssaultiveFelony] {
	some af1: AssaultiveFelony - af | some af2: AssaultiveFelony - af - af1 |
		eventually (now = af1 and (eventually (now = af2 and eventually now = af)))
}

-- Does the felony f occur after three preceding felonies?
pred afterThirdFelony[f: Felony] {
	some f1: Felony - f | some f2: Felony - f - f1 | some f3: Felony - f - f1 - f2 |
		eventually (now = f1 and
			(eventually (now = f2 and (eventually now = f3 and eventually now = f))))
}

-- Does the OWI occur after a preceding OWI?
pred afterFirstOWI[owi: OWI] {
	some owi1: OWI - owi |
		eventually (now = owi1 and (eventually now = owi))
}

-- Is the conviction c (eventually) expunged?
pred expunged[c: Conviction] {
	some e: Expungement | c in e.con
}

-- Is an expungement expunging a previously expunged conviction?
pred multExpunge[e: Expungement] {
	--all e1: Expungement - e | all c: Conviction | c in e.con and c in e1.con
}

fact {
	-- Once events stop, they stop forever
	always (no now implies always no now)
	-- Every event occurs exactly once
	all e: Event | eventually (e in now and after always e not in now)
	-- Every expungement is expunging a preceding conviction
	all x: Expungement | eventually (x.con in now and eventually x in now)
	-- Every expungement is expunging a crime that hasn't been expunged yet
	all x: Expungement | all x1: Expungement - x | x.con != x1.con
	-- Crimes are not expunged twice
	all x: Expungement | all x1: Expungement - x | all c: Conviction | c in x.con  => c not in x1.con
	-- Convictions and expungements cannot happen at same time
	-- However, convictions can happen at same time and then later
	-- be expunged at the same time. This is the "One Bad Night Rule"
	all x: Expungement | all c: Conviction | always (c in now => x not in now)
	all x: Expungement | all c: Conviction | always (x in now => c not in now)
}

-- Michiganders with 4 or more felonies are ineligible to set aside *any* convictions (Sec. 1, 1a).
pred sec1_1a {	
	no f: Felony | no c: Conviction | afterThirdFelony[f] and expunged[c]
}

-- Only two assaultive felonies may be expunged (Sec. 1, 1b).
pred sec1_1b {
	no af: AssaultiveFelony | afterSecondAssault[af] and expunged[af]
}

-- Only one ten year felony may be expunged (Sec. 1, 1c).
pred sec1_1c {
	no ty: TenYearFelony | afterFirstTenner[ty] and expunged[ty]
}

-- Only one OWI may be expunged (Sec. 1d, 2abcd).
pred sec1d_2 {
	no owi: OWI | afterFirstOWI[owi] and expunged[owi]
}

-- The constraints of MCL 780.621 hold in the model.
fact {
	sec1d_2 and sec1_1c and sec1_1b and sec1_1a
}

-- Hard coded years
fact {
	-- Commented out for simple examples with Y1, ..., Y4
	-- However, will work in the exact same way for larger cases

	--happensBefore = Y1->(Y2+Y3+Y4+Y5+Y6+Y7+Y8+Y9+Y10) 
	--+ Y2->(Y3+Y4+Y5+Y6+Y7+Y8+Y9+Y10)
	--+ Y3->(Y4+Y5+Y6+Y7+Y8+Y9+Y10)
	--+ Y4->(Y5+Y6+Y7+Y8+Y9+Y10)
	--+ Y5->(Y6+Y7+Y8+Y9+Y10)
	--+ Y6->(Y7+Y8+Y9+Y10)
	--+ Y7->(Y8+Y9+Y10)
	--+ Y8->(Y9+Y10)
	--+ Y9->(Y10)

	--withinThree = Y1->(Y2+Y3)
	--+ Y2->(Y3+Y4)
	--+ Y3->(Y4+Y5)
	--+ Y4->(Y5+Y6)
	--+ Y5->(Y6+Y7)
	--+ Y6->(Y7+Y8)
	--+ Y7->(Y8+Y9)
	--+ Y8->(Y9+Y10)
	--+ Y9->(Y10)

	-- Y1, ..., Y4

	happensBefore = Y1->(Y2+Y3+Y4) 
	+ Y2->(Y3+Y4)
	+ Y3->(Y4)

	withinThree = Y1->(Y2+Y3)
	+ Y2->(Y3+Y4)
	+ Y3->(Y4)
}

pred timeContradiction[e: Event] {
	some e1: Event | e1 in now and eventually e in now and e1.date in e.date.happensBefore
}

-- Well-behaved years
fact {
	-- All elements in now must have the same year
	all e: Event | all e1: Event - e | always (e.date != e1.date => e not in now or e1 not in now) 

	-- All elements not in now must have a different year than those in now
	all e: Event | all e1: Event - e | always (e in now and e1 not in now => e.date != e1.date)

	-- No situations where Y(N) occurs before Y(N-1), i.e. Y2 cannot occur before Y1 
	no e: Event | timeContradiction[e]
}

-- Analyzer searches for all instances which satisfy the show predicate.
pred show {
	some owi : OWI | expunged[owi]
}

run show for 8
