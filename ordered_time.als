open util/ordering[year]

sig year {
	--happensBefore: set year, -- Looks like spaghetti but is correct rel.
	withinThree: set year
}

pred sensicalWorld[y: year] {
	--all y1: year - y | y1 in y.happensBefore <=> y1.lt[y] -- Looks like spaghetti but is correct rel.
	
	y != last => y.next in y.withinThree
	y.next != last => y.next.next in y.withinThree

	#y.withinThree < 3
	y not in y.withinThree
}

fact {
	all y: year | sensicalWorld[y]
	all y: year | all y1: year - y | y1 in y.withinThree => y.lt[y1]
}

pred show { }

run show for 8
