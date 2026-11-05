import EulerNonuniqueness.Section6.PaperPairedExternalTaylor
import EulerNonuniqueness.Section6.PaperExternalFirstMoment

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupole_paired_neutral_memory_rate_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count}
    {horizon time radius length deformation : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (center : ℂ)
    (radiusNonnegative : 0 ≤ radius) (distance : Fin count → ℝ)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ position ∈ Metric.closedBall center radius,
      ∀ source ∈ Finset.univ.erase index, ∀ patch, ∀ location ∈ motion.domain time source patch,
        distance source ≤ ‖position - location‖)
    (centroidsInside : ∀ patch, patchCentroid motion time index patch ∈ Metric.closedBall center radius)
    (firstPair : ‖patchCentroid motion time index 0 - patchCentroid motion time index 3‖ ≤ 2 * length)
    (secondPair : ‖patchCentroid motion time index 1 - patchCentroid motion time index 2‖ ≤ 2 * length)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (sourceBounded : ∀ source ∈ Finset.univ.erase index, ∀ patch, motion.domain time source patch ⊆
      Metric.closedBall (patchCentroid motion time source patch) (2 * scales.radius (source.val + 1)))
    (receiverSmall : ∀ source ∈ Finset.univ.erase index, 8 * scales.radius (index.val + 1) ≤ distance source)
    (sourceSmall : ∀ source ∈ Finset.univ.erase index, 4 * scales.radius (source.val + 1) ≤ distance source)
    (centroidsSeparated : ∀ receiver, ∀ source ∈ Finset.univ.erase index, ∀ patch,
      distance source ≤ ‖patchCentroid motion time index receiver - patchCentroid motion time source patch‖) :
    ‖(4 * scales.circulation (index.val + 1))⁻¹ •
        (∫ position, quadrupoleDensity scales motion time index position •
          biotSavart (externalPatchVorticity scales motion time index) position) -
        fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) center
          (centroidAsymmetry motion time index)‖ ≤
      (∑ source ∈ Finset.univ.erase index,
        4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) * radius * length +
      (4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
        ∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) / distance source ^ 3 := by
  let linear := fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) center
  let velocity := biotSavart (externalPatchVorticity scales motion time index)
  let position := fun patch => patchCentroid motion time index patch
  let residual := fun patch => quadrupoleExternalReceiverResidual scales motion time index patch
  let pointError := velocity (position 0) + velocity (position 1) - velocity (position 2) - velocity (position 3) -
    linear ((4 : ℝ) • centroidAsymmetry motion time index)
  let residualSum := ∑ patch : Fin 4, patchSign patch • residual patch
  let cost := (4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
    ∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) / distance source ^ 3
  have residualBound : ‖residualSum‖ ≤ 4 * cost := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _patch : Fin 4, cost := by
        apply Finset.sum_le_sum
        intro patch _
        have sign : |patchSign patch| = 1 := by fin_cases patch <;> norm_num [patchSign]
        rw [norm_smul, Real.norm_eq_abs, sign, one_mul]
        exact evolution.quadrupoleExternalReceiverResidual_bound inside amplitudePositive frequencyPositive
          ratioPositive index patch distance (control patch) nonnegative small positive sourceBounded
          receiverSmall sourceSmall (centroidsSeparated patch)
      _ = _ := by simp
  have pointBound := evolution.quadrupole_paired_point_external_taylor_bound inside amplitudePositive
    frequencyPositive ratioPositive index center radiusNonnegative distance positive separated centroidsInside firstPair secondPair
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have coefficient : (4 * scales.circulation (index.val + 1))⁻¹ * scales.circulation (index.val + 1) =
      (1 / 4 : ℝ) := by field_simp; ring
  have identity : (4 * scales.circulation (index.val + 1))⁻¹ •
      (∫ location, quadrupoleDensity scales motion time index location • velocity location) -
      linear (centroidAsymmetry motion time index) =
      (1 / 4 : ℝ) • pointError + (1 / 4 : ℝ) • residualSum := by
    rw [evolution.quadrupole_external_integral_eq_centroid_residual_sum inside amplitudePositive
      frequencyPositive ratioPositive index, smul_smul, coefficient]
    dsimp only [pointError]
    rw [linear.map_smul]
    simp only [residualSum, Fin.sum_univ_four,
      show patchSign (0 : Fin 4) = 1 from rfl, show patchSign (1 : Fin 4) = 1 from rfl,
      show patchSign (2 : Fin 4) = -1 from rfl, show patchSign (3 : Fin 4) = -1 from rfl,
      Complex.real_smul, smul_add, smul_sub]
    norm_num
    dsimp only [velocity, position, residual, linear]
    ring
  rw [identity]
  have estimate := (norm_add_le ((1 / 4 : ℝ) • pointError) ((1 / 4 : ℝ) • residualSum)).trans
    (add_le_add (by simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] using
      mul_le_mul_of_nonneg_left pointBound (by norm_num : (0 : ℝ) ≤ 1 / 4))
      (by simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] using
        mul_le_mul_of_nonneg_left residualBound (by norm_num : (0 : ℝ) ≤ 1 / 4)))
  exact estimate.trans_eq (by dsimp only [cost]; ring)

end EulerNonuniqueness.Paper
