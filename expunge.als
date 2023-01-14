module expunge

-- An event is a conviction or expungement
abstract sig Event { }
abstract sig Conviction extends Event { }
abstract sig Felony extends Conviction { }
abstract sig Misdemeanor extends Conviction { }
sig AssaultiveFelony in Felony { }
sig TenYearFelony in Felony { }
sig Expungement extends Event {
	con: one Conviction -- the conviction that is being expunged
}

-- now indicates the current event
var lone sig now in Event { }

-- Does the ten-year felony ty occur after a preceding ten-year felony?
-- NATHAN: takes a 10 yr felony conviction ty. Checks to see if any 10 yr
-- felony conviction ty1 that is not the same as ty occurs. True if so.
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

-- Is the conviction c (eventually) expunged?
-- NATHAN: takes a conviction c. Checks to see if any expungment e can have  
-- an associated conviction c. True if so.
pred expunged[c: Conviction] {
	some e: Expungement | e.con = c
}

fact {
	-- Once events stop, they stop forever
	always (no now implies always no now)
	-- Every event occurs exactly once
	all e: Event | eventually (now = e and after always now != e)
	-- Every expungement is expunging a preceding conviction
	all x: Expungement | eventually (now = x.con and eventually now = x)
}

pred show {
	one ty: TenYearFelony | afterFirstTenner[ty] and expunged[ty]
}

run show for 8
