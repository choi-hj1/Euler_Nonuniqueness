import EulerNonuniqueness.Section6.PairedCenterFieldBound
import EulerNonuniqueness.Section6.PaperCentroidResidualNorm
import EulerNonuniqueness.Section6.FourPointExternalTaylor
import EulerNonuniqueness.Section6.PaperExternalTaylor

noncomputable section

open Set EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 1000000

theorem quadrupoleCenter_refined_relative_deriv_bound {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    {horizon time deformation gap radius : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count)
    (pathInside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label))
    (control : ∀ patch, BoundaryCloseToCircle scales family.patchMotion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (gapPositive : 0 < gap) (radiusSmall : 8 * scales.radius (index.val + 1) ≤ gap)
    (internalSeparated : ∀ receiver source : Fin 4, source ≠ receiver →
      gap ≤ ‖patchCentroid family.patchMotion time index receiver - patchCentroid family.patchMotion time index source‖)
    (distance : Fin count → ℝ)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (sourceBounded : ∀ source ∈ Finset.univ.erase index, ∀ patch, family.patchMotion.domain time source patch ⊆
      Metric.closedBall (patchCentroid family.patchMotion time source patch) (2 * scales.radius (source.val + 1)))
    (receiverSmall : ∀ source ∈ Finset.univ.erase index, 8 * scales.radius (index.val + 1) ≤ distance source)
    (sourceSmall : ∀ source ∈ Finset.univ.erase index, 4 * scales.radius (source.val + 1) ≤ distance source)
    (centroidsSeparated : ∀ receiver source, source ∈ Finset.univ.erase index → ∀ patch,
      distance source ≤ ‖patchCentroid family.patchMotion time index receiver - patchCentroid family.patchMotion time source patch‖)
    (radiusNonnegative : 0 ≤ radius)
    (centroidsBounded : ∀ patch,
      ‖patchCentroid family.patchMotion time index patch - quadrupoleCenter family.patchMotion time index‖ ≤ radius)
    (centerSeparated : ∀ source ∈ Finset.univ.erase index, ∀ patch,
      ∀ location ∈ family.patchMotion.domain time source patch,
        distance source ≤ ‖quadrupoleCenter family.patchMotion time index - location‖)
    (near : ∀ source ∈ Finset.univ.erase index, 2 * radius ≤ distance source) :
    ‖deriv (fun current => quadrupoleCenter family.patchMotion current index) time -
        biotSavart (externalPatchVorticity scales family.patchMotion time index)
          (quadrupoleCenter family.patchMotion time index)‖ ≤
      |scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2| *
          ‖fourPointSignedMoment (fun patch => patchCentroid family.patchMotion time index patch)‖ / gap ^ 2 +
        (∑ source ∈ Finset.univ.erase index,
          4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) * radius ^ 2 +
        (3456 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
          (Real.pi * gap ^ 3) +
          (4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
            ∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) / distance source ^ 3) := by
  let positions := fun patch => patchCentroid family.patchMotion time index patch
  let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
  let center := quadrupoleCenter family.patchMotion time index
  let field := biotSavart (externalPatchVorticity scales family.patchMotion time index)
  let linear := fderiv ℝ field center
  let residual := fun patch => quadrupoleInternalPatchResidual scales family.patchMotion time index patch +
    quadrupoleExternalReceiverResidual scales family.patchMotion time index patch
  let taylor := fourPointExternalTaylorRemainder field center linear positions
  let hessian := ∑ source ∈ Finset.univ.erase index,
    4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)
  have hessianNonnegative : 0 ≤ hessian := Finset.sum_nonneg fun source member =>
    div_nonneg (mul_nonneg (by norm_num) (scales.circulation_pos frequencyPositive ratioPositive _).le)
      (mul_nonneg Real.pi_pos.le (pow_nonneg (positive source member).le _))
  have taylorBound : ‖taylor‖ ≤ hessian * radius ^ 2 := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hessianNonnegative (sq_nonneg radius))).mpr
    intro patch
    have estimate := evolution.externalPatch_biotSavart_fderiv_taylor_bound inside amplitudePositive frequencyPositive
      ratioPositive index distance positive centerSeparated (fun source member =>
        (mul_le_mul_of_nonneg_left (centroidsBounded patch) (by norm_num)).trans (near source member))
    exact estimate.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (centroidsBounded patch) 2) hessianNonnegative)
  have externalBound := (fourPointArithmeticCenter_norm_le taylor).trans taylorBound
  have internalBound := fourPointArithmeticCenter_field_signedMoment_gap_bound coefficient positions gapPositive (by
    intro positivePatch negativePatch positiveSmall negativeLarge
    apply internalSeparated positivePatch negativePatch
    intro equal
    rw [equal] at negativeLarge
    omega)
  have residualBound := (fourPointArithmeticCenter_norm_le residual).trans
    (evolution.quadrupole_deformation_residual_norm_bound inside amplitudePositive frequencyPositive ratioPositive index distance
      control nonnegative small gapPositive radiusSmall internalSeparated positive sourceBounded receiverSmall sourceSmall centroidsSeparated)
  have derivative := fourPointArithmeticCenter_forced_hasDerivAt
    (trajectory := fun current patch => patchCentroid family.patchMotion current index patch)
    (forcing := quadrupoleCentroidForcing scales family.patchMotion time index)
    (fun patch => by simpa only [quadrupoleCentroidForcing, add_assoc] using
      family.patchCentroid_hasDerivAt_point_field evolution inside index patch (pathInside patch) (material patch))
  change HasDerivAt (fun current => quadrupoleCenter family.patchMotion current index)
    (fourPointArithmeticCenter (fourPointField coefficient positions) +
      fourPointArithmeticCenter (quadrupoleCentroidForcing scales family.patchMotion time index)) time at derivative
  have forcingIdentity : fourPointArithmeticCenter (quadrupoleCentroidForcing scales family.patchMotion time index) =
      fourPointArithmeticCenter (fun patch => field (positions patch)) + fourPointArithmeticCenter residual := by
    simp only [fourPointArithmeticCenter, quadrupoleCentroidForcing, residual, positions, field,
      Finset.sum_add_distrib, add_div]
    abel
  have taylorIdentity := fourPointArithmeticCenter_external_taylor field linear positions
  change fourPointArithmeticCenter (fun patch => field (positions patch)) = field center + fourPointArithmeticCenter taylor at taylorIdentity
  rw [derivative.deriv, forcingIdentity, taylorIdentity]
  have identity : fourPointArithmeticCenter (fourPointField coefficient positions) +
      (field center + fourPointArithmeticCenter taylor + fourPointArithmeticCenter residual) - field center =
      (fourPointArithmeticCenter (fourPointField coefficient positions) + fourPointArithmeticCenter taylor) +
        fourPointArithmeticCenter residual := by abel
  rw [identity]
  exact ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)).trans
    (add_le_add (add_le_add internalBound externalBound) residualBound)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
