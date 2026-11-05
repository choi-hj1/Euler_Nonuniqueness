import EulerNonuniqueness.Section5.CascadeCoMovingPreparedPair
import EulerNonuniqueness.Section4.ReferenceMaterialWitness

noncomputable section

namespace EulerNonuniqueness.Paper

structure CascadeMaterialPreparedPair (scales : Scales) (orbit : SeparatingOrbit) (sectionTime : ℝ)
    (phase dipoleAngle : ℕ → ℝ) (threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ)
    (count : ℕ) extends CascadeCoMovingPreparedPair scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count where
  referenceWitness : ReferenceMaterialCoarseWitness scales (fun index : Fin count => phase (index.val + 1))
    threshold referenceConstant
  referenceIdentity : reference = referenceWitness.trajectory.movingFamily.patchMotion
  unstableIdentity : unstable = referenceWitness.unstable

end EulerNonuniqueness.Paper
