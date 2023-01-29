-- nathan and ishaq version

-- TODO

-- "One Bad Night Rule" (Sec. 1b)
-- if there is a moment with multiple expungements, the expungements 
-- are linked to convictions that happen “at the same time”.
-- 

-- 1 < Felony (7 yrs), 1 Felony + Misdemeanors (5 yrs), Misdemeanors (3 yrs) (Sec. 1d)
-- 
 
module expunge

-- An event is a conviction or expungement
abstract sig Event { }
abstract sig Conviction extends Event { }
abstract sig Felony extends Conviction { }
abstract sig Misdemeanor extends Conviction { } 
sig OWI in Misdemeanor { }
sig AssaultiveFelony in Felony { }
sig TenYearFelony in Felony { }
sig Expungement extends Event {
	con: one Conviction -- the conviction that is being expunged
}

-- now indicates the current event
var lone sig now in Event { } 
-- NOTE: adding "set" will not compile. I think "set" actually doesn't make sense
-- here anyways (maybe?). We only want one "now". We want multiple events *in*
-- now. DOES THIS MAKE SENSE - DOUBLE CHECK AND MAYBE SEND EMAIL??

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
	some e: Expungement | e.con = c
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
	-- Convictions and expungements cannot happen at same time
	all x: Expungement | all c: Conviction | c in now => x not in now
	all x: Expungement | all c: Conviction | x in now => c not in now
}

-- Michiganders with 4 or more felonies are ineligible to set aside *any* convictions (Sec. 1, 1a).
-- This is computationally expensive and seems to work (optimize)
fact {
	--all f: Felony | all c: Conviction | afterThirdFelony[f]	=> !expunged[c]
	-- This doesn't seem to work	
	--no f: Felony | no c: Conviction | afterThirdFelony[f] and expunged[c]
}

-- Only two assaultive felonies may be expunged (Sec. 1, 1b).
fact {
	no af: AssaultiveFelony | afterSecondAssault[af] and expunged[af]
}


-- Only one ten year felony may be expunged (Sec. 1, 1c).
fact {
	no ty: TenYearFelony | afterFirstTenner[ty] and expunged[ty]
}

-- Only one OWI may be expunged ().
fact {
	no owi: OWI | afterFirstOWI[owi] and expunged[owi]
}

-- Analyzer searches for all instances which satisfy the show predicate.
pred show {
	
	--some f: Felony | afterThirdFelony[f] and expunged[f]
	--some af: AssaultiveFelony | afterSecondAssault[af] and expunged[af]
	--some ty: TenYearFelony | afterFirstTenner[ty] and expunged[ty]
	--some ty: TenYearFelony | expunged[ty]
	--some owi : OWI | afterFirstOWI[owi] and expunged[owi]
	some owi : OWI | expunged[owi]
}

run show for 8
