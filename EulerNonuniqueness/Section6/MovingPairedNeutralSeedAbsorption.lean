import EulerNonuniqueness.Section6.MovingPairedWeightedMemory
import EulerNonuniqueness.Section6.NeutralMomentFrequencyAbsorption

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

theorem centroidAsymmetry_paired_weighted_seed_absorption
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon finish hessian deformation : ℝ} {strain : ℝ≥0}
    (radius : ℝ) (finishNonnegative : 0 ≤ finish)
    (hessianNonnegative : 0 ≤ hessian)
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
        4 * scales.circulation (source.val + 1) / (Real.pi * distance time source ^ 3)) ≤ hessian)
    (observationDistance : ℝ) (observationPositive : 0 < observationDistance)
    (sourceFrequencyLarge : 1 ≤ scales.omega (index.val + 1))
    (strainSmall : (strain : ℝ) ≤ scales.omega index.val)
    (hessianSmall : hessian * observationDistance ≤ 1 / 16384)
    (sourceRadiusBound : radius ≤ 4 * scales.omega (index.val + 1) * scales.length (index.val + 1))
    (patchRadiusBound : scales.radius (index.val + 1) ≤ scales.length (index.val + 1))
    (initialZero : centroidAsymmetry family.patchMotion 0 index = 0) :
    (16 * scales.circulation (index.val + 1) / (Real.pi * observationDistance ^ 3)) *
      (∫ time in (0 : ℝ)..finish, Real.exp (-(2 * Real.sqrt 2 * scales.omega index.val) * time) *
        ‖centroidAsymmetry family.patchMotion time index‖) ≤
      (1 / 8 : ℝ) * (Real.sqrt 3 * scales.circulation (index.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega index.val ^ 2 * observationDistance ^ 4)) := by
  have receiverPositive := scales.omega_pos frequencyPositive ratioPositive index.val
  have sqrtLower : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have gapPositive : 0 < 2 * Real.sqrt 2 * scales.omega index.val - (strain : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right sqrtLower receiverPositive.le]
  have weighted := family.centroidAsymmetry_paired_weighted_bound scales densityEquation radius
    finishNonnegative hessianNonnegative gapPositive evolution horizonPositive timeRange amplitudePositive frequencyPositive
    ratioPositive inside material index center radiusPositive distance positive separated centroidsInside firstPair secondPair
    control nonnegative small sourceBounded receiverSmall sourceSmall centroidsSeparated strainBound hessianBound
  rw [initialZero, norm_zero, zero_div, add_zero] at weighted
  have estimate := mul_le_mul_of_nonneg_left weighted
    (show 0 ≤ 16 * scales.circulation (index.val + 1) / (Real.pi * observationDistance ^ 3) by
      exact div_nonneg (mul_nonneg (by norm_num) (scales.circulation_pos frequencyPositive ratioPositive _).le)
        (by positivity))
  exact estimate.trans (scales.neutral_moment_weighted_cost_absorption index.val frequencyPositive ratioPositive
    observationPositive hessianNonnegative sourceFrequencyLarge strainSmall hessianSmall sourceRadiusBound patchRadiusBound
    nonnegative small)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily

