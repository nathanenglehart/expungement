module expunge

open util/relation
open util/ordering[Date]	-- Dates are linearly ordered

-- An event is a conviction or an expungement
abstract sig Event { 
	date: one Date -- each event has an associated date
}

-- now indicates the current event
var sig now in Event { } 

-- The strict happens-before relation for events (no reflexive pairs)
pred hb[e1, e2: Event] {
	eventually (e1 in now and after eventually e2 in now)
}

-- Well-behaved events
fact {
	-- Once events stop, they stop forever
	always (no now implies always no now)
	-- Every event occurs exactly once
	all e: Event | eventually (e in now and after always e not in now)
}

-- A conviction is a felony or a misdemeanor
abstract sig Conviction extends Event { }

abstract sig Felony extends Conviction { }
-- Special types of felony: assaultive, ten-year
sig AssaultiveFelony in Felony { }
sig TenYearFelony in Felony { }

abstract sig Misdemeanor extends Conviction { }
-- Special type of misdemeanor: OWI (Operating While Intoxicated)
sig OWI in Misdemeanor { }

sig Expungement extends Event {
	con: some Conviction -- the convictions that are being expunged
	-- note: multiple convictions may be expunged in a single event
}

-- Is the conviction c (eventually) expunged?
pred expunged[c: Conviction] {
	some con.c
}
fun exp: Conviction->Expungement {
	~con
}
