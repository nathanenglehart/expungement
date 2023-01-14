### Documentation for Expungement as Code

This document explains the signatures, predicates, and facts in `expunge.als` which models Michigan statutory expungement law MCL 780.621 (here). 

### Signatures

The signatures contained in `expunge.als` are written below.

```
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
```

An `Event` represents an event at a point in time within the model. An `Event` must either be a `Conviction` or `Expungement`. If an `Event` is a `Conviction`, it must be either a `Felony` or `Misdemeanor`. A felony may be either an `AssaultiveFelony` (assaultive felony) or a `TenYearFelony` (felony punishable by ten years or more). An `Event` may also be an `Expungement`. An `Expungement` contains a relation to one singular `Conviction` which it expunged.

The signature `now` represents the current event in the system. Each `Event` in the model has either zero or one `now`. Only one `Event` in the model has a single `now` and every other `Event` has zero `now`. The `now` signature is mutable, meaning that an `Event` is not static. It may change over time. 

### Predicates

Predicates model specific statements in the statute. So far, the statements included in this model are Sec. 1, Sec. 1a, Sec. 1b, and Sec. 1c. They are as follows below.

### Expungement (Sec. 1)

The predicate written below models the natural language from page one of the statute: “(1) Except as otherwise provided in this act, a person who is convicted of 1 or more criminal offenses may file an application with the convicting court for the entry of an order setting aside 1 or more convictions” (MCL 780.621, 1).

```
pred expunged[c: Conviction] {
    some e: Expungement | e.con = c
}
```

The `expunged` predicate returns true iff. for some `Conviction` c there are one or more `Expungement` e such that the e’s relation to a `Conviction` is to the given `Conviction` c. 

### Third Felony (Sec. 1a)

The predicate written below models the natural language from page one of the statute: “  (a) Except as provided in subdivisions (b) and (c), a person convicted of 1 or more criminal offenses, but not more than a total of 3 felony offenses, in this state, may apply to have all of his or her convictions from this state set aside” (MCL 780.621, 1). 

```
-- Does the felony f occur after three preceding felonies?
pred afterThirdFelony[f: Felony] {
    some f1: Felony - f | some f2: Felony - f - f1 | some f3: Felony - f - f1 - f2 |
   	 eventually (now = f1 and
   		 (eventually (now = f2 and (eventually now = f3 and eventually now = f))))
}
```

TODO

### Assaultive Crimes (Sec. 1b)

The predicate written below models the natural language from page one of the statute: “(b) An applicant may not have more than a total of 2 convictions for an assaultive crime set aside under this act during his or her lifetime” (MCL 780.621, 1). 

```
-- Does the assaultive felony af occur after two preceding assaultive felonies?
pred afterSecondAssault[af: AssaultiveFelony] {
    some af1: AssaultiveFelony - af | some af2: AssaultiveFelony - af - af1 |
   	 eventually (now = af1 and (eventually (now = af2 and eventually now = af)))
}
```

TODO

### Ten Year Offenses (Sec. 1c)

The predicate written below models the natural language from page one of the statute: “(c) An applicant may not have more than 1 felony conviction for the same offense set aside under this section if the offense is punishable by more than 10 years imprisonment” (MCL 780.621, 1). 

```
-- Does the ten-year felony ty occur after a preceding ten-year felony?
pred afterFirstTenner[ty: TenYearFelony] {
    some ty1: TenYearFelony - ty |
   	 eventually (now = ty1 and (eventually now = ty))
}
```

It functions as follows. For some felony ty, and some other felony ty1 that is not ty, the predicate will return true iff. eventually, now (the current time index) is ty and then ty1.


