import EulerNonuniqueness.Section5.CascadeMaterialPreparedPair

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

structure CascadeSourcePreparedPair (requestedCap : ℝ) (scales : Scales) (orbit : SeparatingOrbit)
    (sectionTime : ℝ) (phase dipoleAngle : ℕ → ℝ)
    (threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ) (count : ℕ)
    extends CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count where
  referenceShapeCap : ∀ time ∈ Icc (0 : ℝ) 2, ∀ label,
    ‖(referenceWitness.trajectory.curve time).2.2 label - standardCircleBanach‖ < requestedCap
  monitorCap : monitor ≤ requestedCap

end EulerNonuniqueness.Paper
