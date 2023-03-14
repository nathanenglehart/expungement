open util/ordering[year]

sig year {
	happensBefore: set year,
	withinThree: set year,
	withinFive: set year,
	withinSeven: set year
}

pred sensicalHappensBefore[y: year] {
	all y1: year - y | y1 in y.happensBefore <=> y1.lt[y]
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

pred show { }

run show for 8
