import EulerNonuniqueness.Section6.MovingComplexMomentContinuity
import EulerNonuniqueness.Section6.LaplaceGrowingErrorBound
import EulerNonuniqueness.Section6.NeutralMomentFrequencyAbsorption

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FiniteMovingPatchFamily.reference_neutral_weighted_seed_absorption
    {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    {threshold constant horizon distance : ℝ}
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (constantNonnegative : 0 ≤ constant) (hessianNonnegative : 0 ≤ scales.hessian)
    (coarse : ReferenceCoarseBounds scales family.patchMotion threshold constant)
    (horizonNonnegative : 0 ≤ horizon) (horizonBound : horizon ≤ 2) (distancePositive : 0 < distance)
    (source : Fin count) (sourceFrequencyLarge : 1 ≤ scales.omega (source.val + 1))
    (strainSmall : constant * scales.strain ≤ scales.omega source.val)
    (hessianSmall : (constant * scales.hessian) * distance ≤ 1 / 16384)
    (radiusSmall : scales.radius (source.val + 1) ≤ scales.length (source.val + 1)) :
    let decay := 2 * Real.sqrt 2 * scales.omega source.val
    (16 * scales.circulation (source.val + 1) / (Real.pi * distance ^ 3)) *
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
        ‖centroidAsymmetry family.patchMotion elapsed source‖) ≤
        (1 / 8 : ℝ) * (Real.sqrt 3 * scales.circulation (source.val + 1) ^ 2 /
          (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega source.val ^ 2 * distance ^ 4)) := by
  have receiverPositive := scales.omega_pos frequencyPositive ratioPositive source.val
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (source.val + 1)
  have sqrtLower : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have gapPositive : 0 < 2 * Real.sqrt 2 * scales.omega source.val - constant * scales.strain := by
    nlinarith [mul_le_mul_of_nonneg_right sqrtLower receiverPositive.le]
  have continuous : Continuous (fun elapsed => centroidAsymmetry family.patchMotion elapsed source) :=
    ((((family.patchCentroid_continuous source 0).add (family.patchCentroid_continuous source 1)).sub
      (family.patchCentroid_continuous source 2)).sub (family.patchCentroid_continuous source 3)).div_const 4
  have bound := Section6.laplace_exponential_affine_norm_bound continuous gapPositive
    (show 0 ≤ constant * scales.hessian * scales.length (source.val + 1) ^ 2 by positivity)
    (by norm_num : (0 : ℝ) ≤ 0) horizonNonnegative (by
      intro elapsed inside
      have actual := (coarse.2.1 elapsed ⟨inside.1, inside.2.trans horizonBound⟩ source).2.2.2.2.1
      convert actual using 1 <;> ring)
  simp only [zero_div, add_zero] at bound
  have scalar := scales.neutral_moment_weighted_cost_absorption source.val frequencyPositive ratioPositive
    distancePositive (mul_nonneg constantNonnegative hessianNonnegative) sourceFrequencyLarge strainSmall hessianSmall
    (sourceRadius := scales.length (source.val + 1)) (by
      have lengthPositive := scales.length_pos (source.val + 1)
      nlinarith [mul_le_mul_of_nonneg_right sourceFrequencyLarge lengthPositive.le])
    radiusSmall (deformation := 0) (by norm_num) (by norm_num)
  dsimp only
  exact (mul_le_mul_of_nonneg_left bound (by positivity :
    (0 : ℝ) ≤ 16 * scales.circulation (source.val + 1) / (Real.pi * distance ^ 3))).trans
    (by simpa only [mul_zero, add_zero, ← pow_two, mul_assoc] using scalar)

end EulerNonuniqueness.Paper
