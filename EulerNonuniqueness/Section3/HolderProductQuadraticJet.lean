import EulerNonuniqueness.Section3.HolderDifferentialAlgebra

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem holderProduct_linear_left_jet_identity
    (first increment second secondLinear secondQuadratic secondNext : PeriodicHolderHalf) :
    holderProduct (first + increment) secondNext - holderProduct first second -
        (holderProduct first secondLinear + holderProduct increment second) -
        (holderProduct first secondQuadratic + holderProduct increment secondLinear) =
      holderProduct (first + increment) (secondNext - second - secondLinear - secondQuadratic) +
        holderProduct increment secondQuadratic := by
  apply PeriodicHolderHalf.ext_value
  intro label
  change (first.val.1 label + increment.val.1 label) * secondNext.val.1 label -
      first.val.1 label * second.val.1 label -
      (first.val.1 label * secondLinear.val.1 label + increment.val.1 label * second.val.1 label) -
      (first.val.1 label * secondQuadratic.val.1 label +
        increment.val.1 label * secondLinear.val.1 label) =
    (first.val.1 label + increment.val.1 label) *
      (secondNext.val.1 label - second.val.1 label -
        secondLinear.val.1 label - secondQuadratic.val.1 label) +
      increment.val.1 label * secondQuadratic.val.1 label
  ring

theorem holderProduct_linear_left_jet_norm
    (first increment second secondLinear secondQuadratic secondNext : PeriodicHolderHalf) :
    ‖holderProduct (first + increment) secondNext - holderProduct first second -
        (holderProduct first secondLinear + holderProduct increment second) -
        (holderProduct first secondQuadratic + holderProduct increment secondLinear)‖ ≤
      2 * ‖first + increment‖ * ‖secondNext - second - secondLinear - secondQuadratic‖ +
        2 * ‖increment‖ * ‖secondQuadratic‖ := by
  rw [holderProduct_linear_left_jet_identity]
  exact (norm_add_le _ _).trans
    (add_le_add (holderProduct_norm_bound _ _) (holderProduct_norm_bound _ _))

end

end EulerNonuniqueness.Paper
