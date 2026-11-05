import EulerNonuniqueness.Section6.PaperExternalMomentDynamics
import EulerNonuniqueness.Section6.PaperNeutralTaylorRemainder
import EulerNonuniqueness.Section4.ReferenceCentroidFieldGeometry
import EulerNonuniqueness.Section1.ForeignInteractionWeight

noncomputable section

open Set Metric MeasureTheory
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

theorem FinitePatchEvolution.reference_neutral_derivative_bound_of_boundary_gaps
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (horizonPositive : 0 < horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyLarge : 1 ≤ scales.frequency)
    (ratioLarge : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (control : ∀ current ∈ Icc (0 : ℝ) horizon, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch bound)
    (separated : ∀ current ∈ Icc (0 : ℝ) horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0))
    (index : Fin count) (inside : time ∈ Ioo (0 : ℝ) horizon)
    (geometry : ReferenceCentroidFieldGeometry scales motion time index)
    (receiverBounded : ∀ patch, motion.domain time index patch ⊆
      closedBall (quadrupoleCenter motion time index) (3 * scales.length (index.val + 1))) :
    ‖deriv (fun current => centroidAsymmetry motion current index) time‖ ≤
      (4608 / Real.pi) * scales.strain * ‖centroidAsymmetry motion time index‖ +
        (497664 / Real.pi) * scales.hessian * scales.length (index.val + 1) ^ 2 := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyLarge
  have ratioPositive : 0 < scales.ratio := by linarith
  have lengthPositive := scales.length_pos (index.val + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have closed : time ∈ Icc (0 : ℝ) horizon := ⟨inside.1.le, inside.2.le⟩
  let center := quadrupoleCenter motion time index
  let linear := fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) center
  let coefficient := 4 * scales.circulation (index.val + 1)
  let remainder := ∫ position, quadrupoleDensity scales motion time index position •
    (biotSavart (externalPatchVorticity scales motion time index) position -
      biotSavart (externalPatchVorticity scales motion time index) center - linear (position - center))
  have coefficientPositive : 0 < coefficient := by dsimp only [coefficient]; positivity
  have equation := evolution.centroidAsymmetry_hasDerivAt_external_of_boundary_gaps horizonPositive
    amplitudePositive frequencyPositive ratioPositive
    (fun other => scales.radius_pos amplitudePositive frequencyPositive ratioPositive (other.val + 1))
    control separated index inside
  have identity := evolution.quadrupole_external_first_moment_taylor_identity closed
    amplitudePositive frequencyPositive ratioPositive index center
  have expansion : (∫ position, quadrupoleDensity scales motion time index position •
      biotSavart (externalPatchVorticity scales motion time index) position) =
      linear (coefficient • centroidAsymmetry motion time index) + remainder :=
    (sub_eq_iff_eq_add.mp identity).trans (add_comm _ _)
  have rateIdentity : coefficient⁻¹ • (∫ position,
      quadrupoleDensity scales motion time index position •
        biotSavart (externalPatchVorticity scales motion time index) position) =
      linear (centroidAsymmetry motion time index) + coefficient⁻¹ • remainder := by
    rw [expansion, smul_add, linear.map_smul, smul_smul,
      inv_mul_cancel₀ coefficientPositive.ne', one_smul]
  have remainderBound : ‖coefficient⁻¹ • remainder‖ ≤
      (497664 / Real.pi) * scales.hessian * scales.length (index.val + 1) ^ 2 := by
    have bound := evolution.quadrupole_external_taylor_remainder_bound closed
      amplitudePositive frequencyPositive ratioPositive index center (by positivity)
      receiverBounded (referenceSourceDistance scales index) geometry.positive geometry.centerSeparated geometry.near
    change ‖remainder‖ ≤ coefficient * (∑ source ∈ Finset.univ.erase index,
      4 * scales.circulation (source.val + 1) / (Real.pi * referenceSourceDistance scales index source ^ 3)) *
        (3 * scales.length (index.val + 1)) ^ 2 at bound
    have multiplied := mul_le_mul_of_nonneg_left bound (inv_pos.mpr coefficientPositive).le
    have normalized : ‖coefficient⁻¹ • remainder‖ ≤
        (∑ source ∈ Finset.univ.erase index,
          4 * scales.circulation (source.val + 1) / (Real.pi * referenceSourceDistance scales index source ^ 3)) *
            (3 * scales.length (index.val + 1)) ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr coefficientPositive)]
      exact multiplied.trans_eq (by field_simp; ring)
    exact normalized.trans ((mul_le_mul_of_nonneg_right
      (scales.foreign_hessian_weight_le frequencyLarge ratioLarge alphaPositive index)
      (sq_nonneg _)).trans_eq (by ring))
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  let strain : ℝ≥0 := ⟨(4608 / Real.pi) * scales.strain, by positivity⟩
  have halfWeight : (∑ source ∈ Finset.univ.erase index,
      2 * scales.circulation (source.val + 1) /
        (Real.pi * (referenceSourceDistance scales index source / 2) ^ 2)) ≤ (strain : ℝ) := by
    have identity : (∑ source ∈ Finset.univ.erase index,
        2 * scales.circulation (source.val + 1) /
          (Real.pi * (referenceSourceDistance scales index source / 2) ^ 2)) =
        4 * ∑ source ∈ Finset.univ.erase index,
          2 * scales.circulation (source.val + 1) /
            (Real.pi * referenceSourceDistance scales index source ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro source member
      ring
    rw [identity]
    exact (mul_le_mul_of_nonneg_left
      (scales.foreign_strain_weight_le frequencyLarge ratioLarge alphaPositive index) (by norm_num)).trans_eq (by
        change 4 * ((1152 / Real.pi) * scales.strain) = (4608 / Real.pi) * scales.strain
        ring)
  have lipschitz := evolution.externalPatch_biotSavart_lipschitzOn closed amplitudePositive frequencyPositive
    ratioPositive index (fun source => referenceSourceDistance scales index source / 2)
    (ball center (scales.length (index.val + 1)))
    (fun source member => half_pos (geometry.positive source member)) (by
      intro position positionInside source member patch location locationInside
      have nearPosition : ‖position - center‖ < scales.length (index.val + 1) := by
        simpa only [mem_ball, dist_eq_norm] using positionInside
      have sourceGap := geometry.centerSeparated source member patch location locationInside
      change referenceSourceDistance scales index source ≤ ‖center - location‖ at sourceGap
      have triangle := norm_add_le (center - position) (position - location)
      rw [sub_add_sub_cancel, norm_sub_rev center position] at triangle
      change referenceSourceDistance scales index source / 2 ≤ ‖position - location‖
      have gapLarge := geometry.near source member
      linarith only [sourceGap, triangle, nearPosition, gapLarge, lengthPositive]) halfWeight
  have linearBound : ‖linear‖ ≤ (4608 / Real.pi) * scales.strain :=
    norm_fderiv_le_of_lipschitzOn ℝ (ball_mem_nhds center (scales.length_pos _)) lipschitz
  rw [equation.deriv]
  change ‖coefficient⁻¹ • _‖ ≤ _
  rw [rateIdentity]
  exact (norm_add_le _ _).trans (add_le_add
    ((linear.le_opNorm _).trans (mul_le_mul_of_nonneg_right linearBound (norm_nonneg _))) remainderBound)

end EulerNonuniqueness.Paper
