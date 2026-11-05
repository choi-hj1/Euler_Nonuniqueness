import EulerNonuniqueness.Section6.MovingQuadrupoleMemoryHistory
import EulerNonuniqueness.Section6.LaplaceGrowingErrorBound
import Mathlib.Data.Complex.ExponentialBounds

noncomputable section

open Set MeasureTheory
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem centroidAsymmetry_prehit_bound {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon hit hessian : ℝ} {strain : ℝ≥0}
    (hitNonnegative : 0 ≤ hit) (hitSmall : hit ≤ 1) (strainSmall : (strain : ℝ) ≤ 1)
    (hessianNonnegative : 0 ≤ hessian)
    (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (horizonPositive : 0 < horizon) (timeRange : Icc 0 hit ⊆ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (inside : ∀ time ∈ Icc 0 hit, ∀ index,
      time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ time ∈ Icc 0 hit, ∀ index label,
      (family.patch index).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (index : Fin count) (center : ℝ → ℂ)
    (sourceBounded : ∀ time ∈ Icc 0 hit, ∀ patch,
      family.patchMotion.domain time index patch ⊆ Metric.closedBall (center time)
        (4 * scales.length (index.val + 1)))
    (distance : ℝ → Fin count → ℝ) (region : ℝ → Set ℂ)
    (neighborhood : ∀ time ∈ Icc 0 hit, region time ∈ 𝓝 (center time))
    (positive : ∀ time ∈ Icc 0 hit, ∀ source ∈ Finset.univ.erase index, 0 < distance time source)
    (separated : ∀ time ∈ Icc 0 hit, ∀ position ∈ region time,
      ∀ source ∈ Finset.univ.erase index, ∀ patch,
      ∀ location ∈ family.patchMotion.domain time source patch, distance time source ≤ ‖position - location‖)
    (near : ∀ time ∈ Icc 0 hit, ∀ source ∈ Finset.univ.erase index,
      8 * scales.length (index.val + 1) ≤ distance time source)
    (strainBound : ∀ time ∈ Icc 0 hit,
      (∑ source ∈ Finset.univ.erase index,
        2 * scales.circulation (source.val + 1) / (Real.pi * distance time source ^ 2)) ≤ (strain : ℝ))
    (hessianBound : ∀ time ∈ Icc 0 hit,
      (∑ source ∈ Finset.univ.erase index,
        4 * scales.circulation (source.val + 1) / (Real.pi * distance time source ^ 3)) ≤ hessian)
    (initialZero : centroidAsymmetry family.patchMotion 0 index = 0) :
    ‖centroidAsymmetry family.patchMotion hit index‖ ≤
      64 * hessian * scales.length (index.val + 1) ^ 2 := by
  have lengthPositive := scales.length_pos (index.val + 1)
  have history := family.centroidAsymmetry_memory_history_bound scales densityEquation
    (fun _ => 4 * scales.length (index.val + 1)) continuous_const hitNonnegative evolution horizonPositive
    timeRange amplitudePositive frequencyPositive ratioPositive inside material index center (fun _ _ => by positivity)
    sourceBounded distance region neighborhood positive separated
    (fun time member source membership => by convert near time member source membership using 1; ring)
    strainBound hessianBound hit ⟨hitNonnegative, le_rfl⟩
  rw [initialZero, norm_zero, zero_add] at history
  have integralBound := Section6.exponential_constant_history_integral_bound strain.property
    (mul_nonneg hessianNonnegative (sq_nonneg (4 * scales.length (index.val + 1)))) hitNonnegative
  have growthBound : Real.exp ((strain : ℝ) * hit) ≤ 4 := by
    apply (Real.exp_le_exp.mpr ?_).trans (Real.exp_one_lt_d9.le.trans (by norm_num))
    exact (mul_le_mul strainSmall hitSmall hitNonnegative (by norm_num)).trans_eq (by norm_num)
  have estimate := history.trans (mul_le_mul_of_nonneg_left integralBound (Real.exp_pos _).le)
  have timeBound := mul_le_mul_of_nonneg_left hitSmall
    (mul_nonneg hessianNonnegative (sq_nonneg (4 * scales.length (index.val + 1))))
  apply estimate.trans
  have multiplied := mul_le_mul growthBound timeBound
    (mul_nonneg (mul_nonneg hessianNonnegative (sq_nonneg _)) hitNonnegative) (by norm_num : (0 : ℝ) ≤ 4)
  convert multiplied using 1
  ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
