(:action move
 :parameters (?r ?from ?to)
 :precondition (and (robot ?r) (at ?r ?from) (connected ?from ?to))
 :effect (and (not (at ?r ?from)) (at ?r ?to)))
