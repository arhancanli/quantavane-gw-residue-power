module

import Solution

/-!
# Axiom check

`lake env lean scripts/CheckAxioms.lean` (after `lake build`) prints the axioms that each compared
theorem of `Solution.lean` depends on. Palomar permits only `propext`, `Classical.choice` and
`Quot.sound`.
-/

#print axioms GwPower.theorem4
#print axioms GwPower.exists_goodExactColouring
#print axioms GwPower.lt_of_gwProperty
#print axioms GwPower.lt_GW
#print axioms GwPower.theorem8
#print axioms GwPower.exists_goodExactColouring_split
#print axioms GwPower.lt_of_gwProperty_split
#print axioms GwPower.lt_GW_split
#print axioms GwPower.gw_4_4_4
#print axioms GwPower.gw_5_5_4
#print axioms GwPower.gw_6_6_4
#print axioms GwPower.gw_6_4_4
#print axioms GwPower.gw_8_5_4
