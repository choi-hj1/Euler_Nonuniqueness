import EulerNonuniqueness.Section6.SourcePacketRetainedModel
import EulerNonuniqueness.Section6.MovingPatchWeightedSeedAbsorption

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem Scales.separatingLeadingMoment_eq_physical_ramp (scales : Scales) (index : ℕ)
    (outgoingPhase elapsed : ℝ) :
    separatingLeadingMoment (scales.circulation index) outgoingPhase elapsed =
      scales.circulation index • ((-4 * Complex.I * (scales.omega index : ℂ) *
        (scales.length index : ℂ) ^ 2 * Complex.exp (Complex.I * (outgoingPhase : ℂ)) ^ 2) * (elapsed : ℂ)) := by
  have exponential : Complex.exp (2 * Complex.I * (outgoingPhase : ℂ)) =
      Complex.exp (Complex.I * (outgoingPhase : ℂ)) ^ 2 := by
    convert Complex.exp_nat_mul (Complex.I * (outgoingPhase : ℂ)) 2 using 1 <;> congr 1 <;> ring
  unfold separatingLeadingMoment
  rw [exponential, Complex.real_smul, Scales.circulation]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  <;> ring

theorem source_packet_moment_retains_original_history (initial inherited ramp : ℂ) :
    initial + (inherited - initial) + ramp = inherited + ramp := by abel

theorem source_packet_target_moment_error_eq_physical_ramp {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales) (source : Fin count)
    (start elapsed outgoingPhase : ℝ) :
    let moment := fun time => ∫ position, quadrupoleDensity scales family.patchMotion time source position •
      (position - quadrupoleCenter family.patchMotion time source) ^ 2
    moment (start + elapsed) -
        (moment 0 + (moment start - moment 0) + separatingLeadingMoment (scales.circulation (source.val + 1)) outgoingPhase elapsed) =
      moment (start + elapsed) - moment start - scales.circulation (source.val + 1) •
        ((-4 * Complex.I * (scales.omega (source.val + 1) : ℂ) * (scales.length (source.val + 1) : ℂ) ^ 2 *
          Complex.exp (Complex.I * (outgoingPhase : ℂ)) ^ 2) * (elapsed : ℂ)) := by
  dsimp only
  rw [source_packet_moment_retains_original_history, scales.separatingLeadingMoment_eq_physical_ramp]
  abel

theorem source_packet_moment_history_seed_absorption {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales) (source : Fin count)
    (start horizon outgoingPhase : ℝ) {distance outgoingRadius initialError forcing deformation : ℝ}
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (distancePositive : 0 < distance) (ratioLarge : 1024 ≤ scales.ratio)
    (outgoingRadiusLarge : 2048 ≤ outgoingRadius) (initialErrorSmall : initialError ≤ 1 / 1024)
    (relativeSmall : forcing * horizon ≤ 1 / 4096)
    (centerSmall : forcing * outgoingRadius / scales.omega (source.val + 1) ≤ 1 / 4096)
    (radiusSmall : scales.radius (source.val + 1) ≤ scales.length (source.val + 1))
    (deformationNonnegative : 0 ≤ deformation) (deformationSmall : deformation ≤ 1 / 16) :
    let moment := fun time => ∫ position, quadrupoleDensity scales family.patchMotion time source position •
      (position - quadrupoleCenter family.patchMotion time source) ^ 2
    let decay := 2 * Real.sqrt 2 * scales.omega source.val
    let rate := 20 * scales.omega (source.val + 1) * scales.length (source.val + 1) ^ 2 * initialError +
      83200 * scales.omega (source.val + 1) * scales.length (source.val + 1) ^ 2 / outgoingRadius ^ 2 +
      76 * scales.omega (source.val + 1) * forcing * scales.length (source.val + 1) ^ 2 * horizon +
      36 * forcing * scales.length (source.val + 1) ^ 2 * outgoingRadius
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
      ‖moment (start + elapsed) - moment start - scales.circulation (source.val + 1) •
        ((-4 * Complex.I * (scales.omega (source.val + 1) : ℂ) * (scales.length (source.val + 1) : ℂ) ^ 2 *
          Complex.exp (Complex.I * (outgoingPhase : ℂ)) ^ 2) * (elapsed : ℂ))‖) ≤
      scales.circulation (source.val + 1) * rate / decay ^ 2 +
        1024 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 * deformation / decay →
    (6 / (Real.pi * distance ^ 4)) *
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
        ‖moment (start + elapsed) - (moment 0 + (moment start - moment 0) +
          separatingLeadingMoment (scales.circulation (source.val + 1)) outgoingPhase elapsed)‖) ≤
      (1 / 4 : ℝ) * (Real.sqrt 3 * scales.circulation (source.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega source.val ^ 2 * distance ^ 4)) := by
  dsimp only
  intro physicalRampBound
  simp_rw [source_packet_moment_retains_original_history, scales.separatingLeadingMoment_eq_physical_ramp,
    sub_add_eq_sub_sub]
  exact (mul_le_mul_of_nonneg_left physicalRampBound (by positivity : (0 : ℝ) ≤ 6 / (Real.pi * distance ^ 4))).trans
    (scales.moment_ramp_weighted_cost_absorption source.val frequencyPositive ratioPositive distancePositive ratioLarge
      outgoingRadiusLarge initialErrorSmall relativeSmall centerSmall radiusSmall deformationNonnegative deformationSmall)

end EulerNonuniqueness.Paper
