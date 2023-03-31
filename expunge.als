-- nathan, ishaq version

module expunge

open util/ordering[year]

-- An event is a conviction or expungement that happens during a one year
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
	con: some Conviction -- the convictions that are being expunged
}

-- Linearly ordered time

sig year {
	happensBefore: set year,
	withinThree: set year,
	withinFive: set year,
	withinSeven: set year
}

pred sensicalHappensBefore[y: year] {
	all y1: year - y | y1 in y.happensBefore <=> y1.gt[y]
	y not in y.happensBefore
}

pred sensicalWithinThree[y: year] {
	
	y != last => y.next in y.withinThree
	y.next != last => y.next.next in y.withinThree

	all y1: year - y | y1 in y.withinThree => y.lt[y1]

	#y.withinThree < 3
	y not in y.withinThree
}

pred sensicalWithinFive[y: year] {
	all y1: year - y | y1 in y.withinThree => y1 in y.withinFive
	all y1: year - y | y1 in y.next.withinThree => y1 in y.withinFive
	all y1: year - y | y1 in y.next.next.withinThree => y1 in y.withinFive
	
	all y1: year - y | y1 in y.withinFive => y.lt[y1]

	#y.withinFive < 5
	y not in y.withinFive
}

pred sensicalWithinSeven[y: year] {
	all y1: year - y | y1 in y.withinFive => y1 in y.withinSeven
	all y1: year - y | y1 in y.next.withinFive => y1 in y.withinSeven
	all y1: year - y | y1 in y.next.next.withinFive => y1 in y.withinSeven
	
	all y1: year - y | y1 in y.withinSeven => y.lt[y1]

	#y.withinSeven < 7
	y not in y.withinSeven
}

fact {
	all y: year | sensicalHappensBefore[y]
	all y: year | sensicalWithinThree[y]
	all y: year | sensicalWithinFive[y]
	all y: year | sensicalWithinSeven[y]
}

-- now indicates the current event
var sig now in Event { } 

-- Does the ten-year felony ty occur after a preceding ten-year felony?
pred afterFirstTenner[ty: TenYearFelony] {
	some ty1: TenYearFelony - ty | 
		eventually (ty1 in now and (eventually ty in now))
}

-- Does the assaultive felony af occur after two preceding assaultive felonies?
pred afterSecondAssault[af: AssaultiveFelony] {
	some af1: AssaultiveFelony - af | some af2: AssaultiveFelony - af - af1 |
		eventually (af1 in now and (eventually (af2 in now and eventually af in now)))
}

-- Does the felony f occur after three preceding felonies?
pred afterThirdFelony[f: Felony] {
	some f1: Felony - f | some f2: Felony - f - f1 | some f3: Felony - f - f1 - f2 |
		eventually (f1 in now and (eventually (f2 in now and (eventually f3 in now and eventually f in now)))) 
}

-- Does the OWI occur after a preceding OWI?
pred afterFirstOWI[owi: OWI] {
	some owi1: OWI - owi |
		eventually (owi1 in now and (eventually owi in now))
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
}

fact {
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
	sec1d_2
	sec1_1c 
	sec1_1b 
	sec1_1a
}

-- now must go through years in chronological order i.e. now is in Y(N-1) before Y(N) for 1 =< N =< 10
pred timeContradiction[e: Event] {
	some e1: Event | e1 in now and eventually e in now and e1.date in e.date.happensBefore
}

-- Well-behaved years
fact {
	-- All elements in now must have the same year
	all e: Event | all e1: Event - e | always (e.date != e1.date => e not in now or e1 not in now) 

	-- double check. This may be too restrictive
	-- All elements not in now must have a different year than those in now
	all e: Event | all e1: Event - e | always (e in now and e1 not in now => e.date != e1.date)

	-- No situations where Y(N) occurs before Y(N-1), i.e. Y2 cannot occur before Y1 
	no e: Event | timeContradiction[e]
}

-- Timing for Expungements: 1 < Felony (7 yrs), 1 Felony + Misdemeanors (5 yrs), Misdemeanors (3 yrs) (Sec. 1d)
fact {
	no e: Expungement | e.con.date -> e.date in withinThree -- Misdemeanor
	--no e: Expungement | e.con in Misdemeanor and e.con.date -> e.date in withinThree -- withinFive
}

-- add predicates to check scenarios. Assert that what we expect should happen will happen
-- Analyzer searches for all instances which satisfy the show predicate.
pred show {
	some f: Felony | expunged[f]
	--some owi : OWI | expunged[owi]
}

run show for 8
