import EulerNonuniqueness.Section6.MovingPairedMemoryHistory
import EulerNonuniqueness.Section6.LaplaceGrowingErrorBound

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

theorem centroidAsymmetry_paired_weighted_bound
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon finish hessian deformation decay : ℝ} {strain : ℝ≥0}
    (radius : ℝ) (finishNonnegative : 0 ≤ finish)
    (hessianNonnegative : 0 ≤ hessian) (gapPositive : 0 < decay - (strain : ℝ))
    (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (horizonPositive : 0 < horizon) (timeRange : Icc 0 finish ⊆ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (inside : ∀ time ∈ Icc 0 finish, ∀ index,
      time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ time ∈ Icc 0 finish, ∀ index label,
      (family.patch index).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (index : Fin count) (center : ℝ → ℂ) (radiusPositive : 0 < radius)
    (distance : ℝ → Fin count → ℝ)
    (positive : ∀ time ∈ Icc 0 finish, ∀ source ∈ Finset.univ.erase index, 0 < distance time source)
    (separated : ∀ time ∈ Icc 0 finish, ∀ position ∈ Metric.closedBall (center time) (radius),
      ∀ source ∈ Finset.univ.erase index, ∀ patch,
      ∀ location ∈ family.patchMotion.domain time source patch, distance time source ≤ ‖position - location‖)
    (centroidsInside : ∀ time ∈ Icc 0 finish, ∀ patch,
      patchCentroid family.patchMotion time index patch ∈ Metric.closedBall (center time) (radius))
    (firstPair : ∀ time ∈ Icc 0 finish,
      ‖patchCentroid family.patchMotion time index 0 - patchCentroid family.patchMotion time index 3‖ ≤
        2 * scales.length (index.val + 1))
    (secondPair : ∀ time ∈ Icc 0 finish,
      ‖patchCentroid family.patchMotion time index 1 - patchCentroid family.patchMotion time index 2‖ ≤
        2 * scales.length (index.val + 1))
    (control : ∀ time ∈ Icc 0 finish, ∀ patch,
      BoundaryCloseToCircle scales family.patchMotion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (sourceBounded : ∀ time ∈ Icc 0 finish, ∀ source ∈ Finset.univ.erase index, ∀ patch,
      family.patchMotion.domain time source patch ⊆ Metric.closedBall
        (patchCentroid family.patchMotion time source patch) (2 * scales.radius (source.val + 1)))
    (receiverSmall : ∀ time ∈ Icc 0 finish, ∀ source ∈ Finset.univ.erase index,
      8 * scales.radius (index.val + 1) ≤ distance time source)
    (sourceSmall : ∀ time ∈ Icc 0 finish, ∀ source ∈ Finset.univ.erase index,
      4 * scales.radius (source.val + 1) ≤ distance time source)
    (centroidsSeparated : ∀ time ∈ Icc 0 finish, ∀ receiver, ∀ source ∈ Finset.univ.erase index, ∀ patch,
      distance time source ≤ ‖patchCentroid family.patchMotion time index receiver -
        patchCentroid family.patchMotion time source patch‖)
    (strainBound : ∀ time ∈ Icc 0 finish,
      (∑ source ∈ Finset.univ.erase index,
        2 * scales.circulation (source.val + 1) / (Real.pi * distance time source ^ 2)) ≤ (strain : ℝ))
    (hessianBound : ∀ time ∈ Icc 0 finish,
      (∑ source ∈ Finset.univ.erase index,
        4 * scales.circulation (source.val + 1) / (Real.pi * distance time source ^ 3)) ≤ hessian) :
    (∫ time in (0 : ℝ)..finish, Real.exp (-decay * time) *
      ‖centroidAsymmetry family.patchMotion time index‖) ≤
      hessian * (radius * scales.length (index.val + 1) +
        1024 * scales.radius (index.val + 1) ^ 2 * deformation) / (decay - (strain : ℝ)) ^ 2 +
      ‖centroidAsymmetry family.patchMotion 0 index‖ / (decay - (strain : ℝ)) := by
  have history := family.centroidAsymmetry_paired_memory_history scales densityEquation
    (fun _ => radius) continuous_const finishNonnegative evolution horizonPositive timeRange
    amplitudePositive frequencyPositive ratioPositive inside material index center (fun _ _ => radiusPositive)
    distance positive separated centroidsInside firstPair secondPair control nonnegative small sourceBounded
    receiverSmall sourceSmall centroidsSeparated strainBound hessianBound
  have continuous : Continuous (fun time => centroidAsymmetry family.patchMotion time index) := by
    unfold centroidAsymmetry
    exact ((((family.patchCentroid_continuous index 0).add
      (family.patchCentroid_continuous index 1)).sub
      (family.patchCentroid_continuous index 2)).sub
      (family.patchCentroid_continuous index 3)).div_const 4
  have costNonnegative : 0 ≤ hessian * (radius * scales.length (index.val + 1) +
      1024 * scales.radius (index.val + 1) ^ 2 * deformation) :=
    mul_nonneg hessianNonnegative (add_nonneg
      (mul_nonneg radiusPositive.le (scales.length_pos _).le)
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) nonnegative))
  apply Section6.laplace_exponential_affine_norm_bound continuous gapPositive costNonnegative
    (norm_nonneg _) finishNonnegative
  intro time member
  have integralBound := Section6.exponential_constant_history_integral_bound strain.property
    costNonnegative member.1
  exact (history time member).trans
    ((mul_le_mul_of_nonneg_left (add_le_add_left integralBound _) (Real.exp_pos _).le).trans_eq (by ring))

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily

