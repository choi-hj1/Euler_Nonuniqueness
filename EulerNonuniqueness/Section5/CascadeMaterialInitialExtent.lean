import EulerNonuniqueness.Section5.CascadeMaterialPreparedPair
import EulerNonuniqueness.Section5.CascadeCoMovingInitialMonitors
import EulerNonuniqueness.Section5.CascadeBlockExtentEvolution
import EulerNonuniqueness.Section3.MovingCentroidGaugeInitialData

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Paper

theorem CascadeMaterialPreparedPair.initial_extent_bound
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (thresholdSmall : threshold ≤ 1 / 2) {bound : ℝ} (boundThree : 3 ≤ bound)
    (positiveBound : ‖orbit.positive sectionTime‖ ≤ bound)
    (negativeBound : ‖orbit.negative sectionTime‖ ≤ bound) (index : Fin count) :
    ‖prepared.trajectory.blockExtentVector index 0‖ ≤ bound * scales.length (index.val + 1) := by
  have boundNonnegative : 0 ≤ bound * scales.length (index.val + 1) := by
    have lengthPositive := scales.length_pos (index.val + 1)
    positivity
  apply (pi_norm_le_iff_of_nonneg boundNonnegative).mpr
  intro patch
  have identity : prepared.trajectory.blockExtentVector index 0 patch =
      cascadeInitialCenter scales orbit sectionTime (fun index => phase (index.val + 1)) prepared.unstable
        (dipoleAngle count) (index, patch) - (scales.location (index.val + 1) : ℂ) := by
    unfold MovingCentroidGaugeTrajectory.blockExtentVector
    simp only [prepared.trajectory.center_initial, Equiv.symm_apply_apply]
    rw [show (∑ source : Fin 4, cascadeInitialCenter scales orbit sectionTime
        (fun index => phase (index.val + 1)) prepared.unstable (dipoleAngle count) (index, source)) / 4 =
        (scales.location (index.val + 1) : ℂ) from
      cascadeBlockCenter_initial scales orbit sectionTime _ prepared.unstable _ index]
  rw [identity]
  exact cascadeInitialCenter_offset_bound scales orbit sectionTime _ prepared.unstable _ bound
    (fun index => (prepared.referenceInitial index).1.trans thresholdSmall)
    boundThree positiveBound negativeBound (index, patch)

end EulerNonuniqueness.Paper
