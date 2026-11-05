import EulerNonuniqueness.Section6.PaperExternalTaylor
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.externalPatch_paired_taylor_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time radius : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (center first second : ℂ)
    (radiusNonnegative : 0 ≤ radius) (distance : Fin count → ℝ)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ position ∈ Metric.closedBall center radius,
      ∀ source ∈ Finset.univ.erase index, ∀ patch, ∀ location ∈ motion.domain time source patch,
        distance source ≤ ‖position - location‖)
    (firstInside : first ∈ Metric.closedBall center radius)
    (secondInside : second ∈ Metric.closedBall center radius) :
    ‖biotSavart (externalPatchVorticity scales motion time index) first -
        biotSavart (externalPatchVorticity scales motion time index) second -
        fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) center (first - second)‖ ≤
      (∑ source ∈ Finset.univ.erase index,
        4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) * radius * ‖first - second‖ := by
  let linear := fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) center
  let remainder := fun position => biotSavart (externalPatchVorticity scales motion time index) position - linear position
  let coefficient := ∑ source ∈ Finset.univ.erase index,
    4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)
  have coefficientNonnegative : 0 ≤ coefficient := by
    apply Finset.sum_nonneg
    intro source member
    exact div_nonneg (mul_nonneg (by norm_num)
      (scales.circulation_pos frequencyPositive ratioPositive _).le)
      (mul_nonneg Real.pi_pos.le (pow_nonneg (positive source member).le _))
  have centerInside : center ∈ Metric.closedBall center radius := Metric.mem_closedBall_self radiusNonnegative
  have derivative (position : ℂ) (member : position ∈ Metric.closedBall center radius) :
      HasFDerivWithinAt remainder
        (fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) position - linear)
        (Metric.closedBall center radius) position := by
    exact (((evolution.externalPatch_biotSavart_hasFDerivAt inside index distance positive
      (separated position member)).differentiableAt.hasFDerivAt).sub linear.hasFDerivAt).hasFDerivWithinAt
  have derivativeBound (position : ℂ) (member : position ∈ Metric.closedBall center radius) :
      ‖fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) position - linear‖ ≤
        coefficient * radius := by
    have estimate := evolution.externalPatch_biotSavart_fderiv_difference_bound inside amplitudePositive
      frequencyPositive ratioPositive index distance positive (separated position member) (separated center centerInside)
    exact estimate.trans (mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using member) coefficientNonnegative)
  have estimate := (convex_closedBall center radius).norm_image_sub_le_of_norm_hasFDerivWithin_le
    derivative derivativeBound secondInside firstInside
  have identity : remainder first - remainder second =
      biotSavart (externalPatchVorticity scales motion time index) first -
        biotSavart (externalPatchVorticity scales motion time index) second - linear (first - second) := by
    dsimp only [remainder]
    rw [map_sub]
    abel
  rw [identity] at estimate
  exact estimate

theorem FinitePatchEvolution.quadrupole_paired_point_external_taylor_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time radius length : ℝ}
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
    (secondPair : ‖patchCentroid motion time index 1 - patchCentroid motion time index 2‖ ≤ 2 * length) :
    ‖biotSavart (externalPatchVorticity scales motion time index) (patchCentroid motion time index 0) +
        biotSavart (externalPatchVorticity scales motion time index) (patchCentroid motion time index 1) -
        biotSavart (externalPatchVorticity scales motion time index) (patchCentroid motion time index 2) -
        biotSavart (externalPatchVorticity scales motion time index) (patchCentroid motion time index 3) -
        fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) center
          ((4 : ℝ) • centroidAsymmetry motion time index)‖ ≤
      4 * (∑ source ∈ Finset.univ.erase index,
        4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) * radius * length := by
  let linear := fderiv ℝ (biotSavart (externalPatchVorticity scales motion time index)) center
  let coefficient := ∑ source ∈ Finset.univ.erase index,
    4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)
  let velocity := biotSavart (externalPatchVorticity scales motion time index)
  let position := fun patch => patchCentroid motion time index patch
  have coefficientNonnegative : 0 ≤ coefficient := by
    apply Finset.sum_nonneg
    intro source member
    exact div_nonneg (mul_nonneg (by norm_num)
      (scales.circulation_pos frequencyPositive ratioPositive _).le)
      (mul_nonneg Real.pi_pos.le (pow_nonneg (positive source member).le _))
  have first := evolution.externalPatch_paired_taylor_bound inside amplitudePositive frequencyPositive
    ratioPositive index center (position 0) (position 3) radiusNonnegative distance positive separated
    (centroidsInside 0) (centroidsInside 3)
  have second := evolution.externalPatch_paired_taylor_bound inside amplitudePositive frequencyPositive
    ratioPositive index center (position 1) (position 2) radiusNonnegative distance positive separated
    (centroidsInside 1) (centroidsInside 2)
  have moment : position 0 - position 3 + (position 1 - position 2) =
      (4 : ℝ) • centroidAsymmetry motion time index := by
    simp only [position, centroidAsymmetry, Complex.real_smul]
    push_cast
    ring
  have identity : velocity (position 0) + velocity (position 1) - velocity (position 2) - velocity (position 3) -
      linear ((4 : ℝ) • centroidAsymmetry motion time index) =
      (velocity (position 0) - velocity (position 3) - linear (position 0 - position 3)) +
      (velocity (position 1) - velocity (position 2) - linear (position 1 - position 2)) := by
    rw [← moment, map_add]
    abel
  change ‖velocity (position 0) + velocity (position 1) - velocity (position 2) - velocity (position 3) -
    linear ((4 : ℝ) • centroidAsymmetry motion time index)‖ ≤ 4 * coefficient * radius * length
  rw [identity]
  exact (norm_add_le _ _).trans ((add_le_add first second).trans
    ((add_le_add (mul_le_mul_of_nonneg_left firstPair (mul_nonneg coefficientNonnegative radiusNonnegative))
      (mul_le_mul_of_nonneg_left secondPair (mul_nonneg coefficientNonnegative radiusNonnegative))).trans_eq (by ring)))

end EulerNonuniqueness.Paper
