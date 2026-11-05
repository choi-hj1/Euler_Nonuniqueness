import EulerNonuniqueness
import Comparator

/-!
# Publication acceptance check

This file compiles only when `theorem11` supplies a closed proof of the exact
target. It is a verification test, not a declaration or admission of that proof.
-/

example : EulerNonuniqueness.Theorem11 := EulerNonuniqueness.theorem11

#print axioms EulerNonuniqueness.theorem11

example : EulerNonuniquenessChallenge.Target :=
  EulerNonuniquenessComparator.target_iff.mp EulerNonuniqueness.theorem11
