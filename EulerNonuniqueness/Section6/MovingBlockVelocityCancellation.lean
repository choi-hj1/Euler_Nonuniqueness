import EulerNonuniqueness.Section6.MovingBlockRelativeCentroid
import EulerNonuniqueness.Section6.FourPointSpeedBound
import EulerNonuniqueness.Section6.MovingExternalPatchField

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem centered_velocity_bound_of_common_anchor (velocity : Fin 4 → ℂ) (anchor : ℂ)
    {bound : ℝ} (bounded : ∀ source, ‖velocity source - anchor‖ ≤ bound) (patch : Fin 4) :
    ‖velocity patch - (∑ source : Fin 4, velocity source) / 4‖ ≤ 2 * bound := by
  have pairwise (source : Fin 4) : ‖velocity patch - velocity source‖ ≤ 2 * bound := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub (velocity patch) anchor (velocity source)
    rw [norm_sub_rev anchor (velocity source)] at triangle
    linarith [bounded patch, bounded source]
  have estimate := centered_four_velocity_norm_le velocity patch pairwise
  have identity : (∑ source : Fin 4, (velocity patch - velocity source)) / 4 =
      velocity patch - (∑ source : Fin 4, velocity source) / 4 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rwa [identity] at estimate

theorem patchCentroid_relative_velocity_bound {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count)
    (pathInside : ∀ patch, time ∈ Ioo
      (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label,
      (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
        biotSavart (Paper.patchVorticity scales family.patchMotion time)
          ((family.patch (finProdFinEquiv (index, patch))).boundary time label))
    {gap extent internalError externalError : ℝ} (gapPositive : 0 < gap)
    (internalGap : ∀ target source : Fin 4, source ≠ target → gap ≤
      ‖patchCentroid family.patchMotion time index target - patchCentroid family.patchMotion time index source‖)
    (extentBound : ∀ patch, ‖patchCentroid family.patchMotion time index patch -
      quadrupoleCenter family.patchMotion time index‖ ≤ extent)
    (internalBound : ∀ patch, ‖quadrupoleInternalPatchResidual scales family.patchMotion time index patch‖ ≤ internalError)
    (externalBound : ∀ patch, ‖quadrupoleExternalReceiverResidual scales family.patchMotion time index patch‖ ≤ externalError)
    (distance : Fin count → ℝ)
    (distancePositive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (patchSeparated : ∀ patch source, source ∈ Finset.univ.erase index → ∀ sourcePatch,
      ∀ position ∈ family.patchMotion.domain time source sourcePatch,
      distance source ≤ ‖patchCentroid family.patchMotion time index patch - position‖)
    (centerSeparated : ∀ source ∈ Finset.univ.erase index, ∀ sourcePatch,
      ∀ position ∈ family.patchMotion.domain time source sourcePatch,
      distance source ≤ ‖quadrupoleCenter family.patchMotion time index - position‖)
    (patch : Fin 4) :
    ‖deriv (fun current => patchCentroid family.patchMotion current index patch -
        quadrupoleCenter family.patchMotion current index) time‖ ≤
      2 * (4 * |scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2| / gap +
        internalError + externalError +
        (∑ source ∈ Finset.univ.erase index,
          2 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 2)) * extent) := by
  let velocity := fun target : Fin 4 =>
    Section6.fourPointField (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
      (fun source => patchCentroid family.patchMotion time index source) target +
    biotSavart (externalPatchVorticity scales family.patchMotion time index)
      (patchCentroid family.patchMotion time index target) +
    quadrupoleInternalPatchResidual scales family.patchMotion time index target +
    quadrupoleExternalReceiverResidual scales family.patchMotion time index target
  have derivatives (target : Fin 4) :
      HasDerivAt (fun current => patchCentroid family.patchMotion current index target) (velocity target) time :=
    family.patchCentroid_hasDerivAt_point_field evolution inside index target (pathInside target) (material target)
  have derivative := (derivatives patch).sub
    ((HasDerivAt.sum (u := Finset.univ) fun target _ => derivatives target).div_const 4)
  change HasDerivAt (fun current => patchCentroid family.patchMotion current index patch -
    quadrupoleCenter family.patchMotion current index) _ time at derivative
  rw [derivative.deriv]
  apply centered_velocity_bound_of_common_anchor velocity
    (biotSavart (externalPatchVorticity scales family.patchMotion time index)
      (quadrupoleCenter family.patchMotion time index))
  intro target
  have external := (evolution.externalPatch_biotSavart_bounds inside amplitudePositive frequencyPositive
    ratioPositive index distance distancePositive (patchSeparated target) centerSeparated).2
  have nonnegative : 0 ≤ ∑ source ∈ Finset.univ.erase index,
      2 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 2) := by
    apply Finset.sum_nonneg
    intro source member
    have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (source.val + 1)
    positivity
  have externalEstimate := external.trans (mul_le_mul_of_nonneg_left (extentBound target) nonnegative)
  have speed := Section6.fourPointField_norm_le
    (coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
    (fun source => patchCentroid family.patchMotion time index source) gapPositive target (internalGap target)
  dsimp only [velocity]
  have identity (point external internal receiver anchor : ℂ) :
      point + external + internal + receiver - anchor =
        ((point + (external - anchor)) + internal) + receiver := by ring
  rw [identity]
  calc
    _ ≤ ‖Section6.fourPointField
          (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (fun source => patchCentroid family.patchMotion time index source) target‖ +
        ‖biotSavart (externalPatchVorticity scales family.patchMotion time index)
            (patchCentroid family.patchMotion time index target) -
          biotSavart (externalPatchVorticity scales family.patchMotion time index)
            (quadrupoleCenter family.patchMotion time index)‖ +
        ‖quadrupoleInternalPatchResidual scales family.patchMotion time index target‖ +
        ‖quadrupoleExternalReceiverResidual scales family.patchMotion time index target‖ := by
      exact (norm_add_le _ _).trans (add_le_add_right
        ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)) _)
    _ ≤ _ := by linarith [internalBound target, externalBound target]

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
