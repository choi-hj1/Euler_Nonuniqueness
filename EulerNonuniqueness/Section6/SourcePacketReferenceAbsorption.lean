import EulerNonuniqueness.Section6.SourcePacketReferenceMoment
import EulerNonuniqueness.Section6.MovingComplexMomentContinuity
import EulerNonuniqueness.Section6.InitialMomentFrequencyAbsorption
import EulerNonuniqueness.Section6.LaplaceMomentErrorBound

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FiniteMovingPatchFamily.reference_literal_moment_weighted_seed_absorption
    {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    {threshold constant horizon distance : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion 2)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioLarge : 3072 ≤ scales.ratio) (constantNonnegative : 0 ≤ constant)
    (thresholdSmall : threshold ≤ 1 / 4)
    (coarse : ReferenceCoarseBounds scales family.patchMotion threshold constant)
    (horizonNonnegative : 0 ≤ horizon) (horizonBound : horizon ≤ 2) (distancePositive : 0 < distance)
    (source : Fin count)
    (radiusSmall : scales.radius (source.val + 1) ≤ scales.length (source.val + 1))
    (deformationSmall : constant * (scales.omega (source.val + 1))⁻¹ ^ 2 ≤ 1 / 16) :
    let decay := 2 * Real.sqrt 2 * scales.omega source.val
    (6 / (Real.pi * distance ^ 4)) *
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
        ‖∫ position, quadrupoleDensity scales family.patchMotion elapsed source position •
          (position - quadrupoleCenter family.patchMotion elapsed source) ^ 2‖) ≤
        (1 / 8 : ℝ) * (Real.sqrt 3 * scales.circulation (source.val + 1) ^ 2 /
          (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega source.val ^ 2 * distance ^ 4)) := by
  have ratioPositive : 0 < scales.ratio := by linarith
  let envelope := 16 * scales.circulation (source.val + 1) * scales.length (source.val + 1) ^ 2 +
    512 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 *
      (constant * (scales.omega (source.val + 1))⁻¹ ^ 2)
  have envelopeNonnegative : 0 ≤ envelope := by
    dsimp only [envelope]
    have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (source.val + 1)
    positivity
  have bound := Section6.laplace_norm_error_integral_bound
    (family.quadrupole_complex_moment_continuous scales source)
    (show 0 < 2 * Real.sqrt 2 * scales.omega source.val by
      have omegaPositive := scales.omega_pos frequencyPositive ratioPositive source.val
      positivity)
    (by norm_num : (0 : ℝ) ≤ 0) envelopeNonnegative horizonNonnegative (by
      intro elapsed inside
      simpa only [zero_mul, zero_add, envelope] using
        evolution.reference_literal_complex_moment_bound ⟨inside.1, inside.2.trans horizonBound⟩
          amplitudePositive frequencyPositive ratioPositive constantNonnegative thresholdSmall coarse source deformationSmall)
  simp only [zero_div, zero_add] at bound
  have scalar := scales.initial_moment_weighted_cost_absorption source.val frequencyPositive ratioPositive
    distancePositive (outgoingRadius := 32) (by norm_num) (by norm_num; exact ratioLarge) radiusSmall
    (by positivity) deformationSmall (envelope : ℂ) (by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg envelopeNonnegative]
      dsimp only [envelope]
      have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (source.val + 1)
      nlinarith [sq_nonneg (scales.length (source.val + 1))])
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg envelopeNonnegative] at scalar
  dsimp only
  exact (mul_le_mul_of_nonneg_left bound (by positivity : (0 : ℝ) ≤ 6 / (Real.pi * distance ^ 4))).trans
    (by convert scalar using 1 <;> ring)

end EulerNonuniqueness.Paper
