import EulerNonuniqueness.Section6.QuadrupoleFarField
import EulerNonuniqueness.Section2.SeparatingScattering

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

theorem separating_complex_moment_growth (frequency : ℝ) (frequencyPositive : 0 < frequency)
    (circulation : ℝ) :
    ∃ angle : ℝ, ∃ momentOffset : ℂ, ∃ bound > (0 : ℝ), ∃ timeMin > (0 : ℝ),
      ∀ time, timeMin ≤ time →
      ‖quadrupoleComplexMoment circulation (separatingPositive frequency frequencyPositive time)
          (separatingNegative frequency frequencyPositive time) +
        4 * Complex.I * (circulation : ℂ) * (frequency : ℂ) *
          Complex.exp (2 * Complex.I * (angle : ℂ)) * (time : ℂ) - momentOffset‖ ≤ bound / time := by
  obtain ⟨angle, offset, scatteringBound, scatteringPositive, scatteringTime, scatteringTimePositive, scattering⟩ :=
    separating_scattering_asymptotics frequency frequencyPositive
  let limit := Complex.exp (Complex.I * (angle : ℂ))
  have limitNorm : ‖limit‖ = 1 := by simp [limit, Complex.norm_exp]
  let bound := 1 + 4 * |circulation| * (2 * scatteringBound + scatteringBound * (frequency + ‖offset‖))
  refine ⟨angle, 4 * (circulation : ℂ) * offset * limit, bound, by dsimp [bound]; positivity,
    max scatteringTime 1, lt_of_lt_of_le scatteringTimePositive (le_max_left _ _), ?_⟩
  intro time timeAbove
  have timeOne : 1 ≤ time := (le_max_right _ _).trans timeAbove
  have timePositive : 0 < time := by linarith
  have errors := scattering time ((le_max_left _ _).trans timeAbove)
  let separation := separatingPositive frequency frequencyPositive time + separatingNegative frequency frequencyPositive time
  let center := (separatingPositive frequency frequencyPositive time - separatingNegative frequency frequencyPositive time) / 2
  let affine := -Complex.I * (frequency : ℂ) * limit * (time : ℂ) + offset
  have separationBound : ‖separation‖ ≤ 2 :=
    (separatingDipoleSeparation_norm_bounds frequency frequencyPositive time).2
  have affineBound : ‖affine‖ ≤ (frequency + ‖offset‖) * time := by
    calc
      _ ≤ ‖-Complex.I * (frequency : ℂ) * limit * (time : ℂ)‖ + ‖offset‖ := norm_add_le _ _
      _ = frequency * time + ‖offset‖ := by
        simp [norm_mul, limitNorm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos frequencyPositive, abs_of_pos timePositive]
      _ ≤ (frequency + ‖offset‖) * time := by nlinarith [norm_nonneg offset]
  have centerError : ‖center - affine‖ ≤ scatteringBound / time := by
    convert errors.2 using 1
    congr 1
    dsimp [center, affine, limit]
    ring
  have separationError : ‖separation - limit‖ ≤ scatteringBound / time ^ 2 := errors.1
  have identity : quadrupoleComplexMoment circulation
      (separatingPositive frequency frequencyPositive time) (separatingNegative frequency frequencyPositive time) +
      4 * Complex.I * (circulation : ℂ) * (frequency : ℂ) *
        Complex.exp (2 * Complex.I * (angle : ℂ)) * (time : ℂ) -
        4 * (circulation : ℂ) * offset * limit =
      4 * (circulation : ℂ) * ((center - affine) * separation + affine * (separation - limit)) := by
    have exponentialIdentity : Complex.exp (2 * Complex.I * (angle : ℂ)) = limit ^ 2 := by
      rw [show 2 * Complex.I * (angle : ℂ) = Complex.I * (angle : ℂ) + Complex.I * (angle : ℂ) by ring,
        Complex.exp_add]
      dsimp [limit]
      ring
    rw [exponentialIdentity]
    dsimp [quadrupoleComplexMoment, center, affine, separation]
    ring
  rw [identity, norm_mul, norm_mul]
  simp only [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ 4 * |circulation| * (‖(center - affine) * separation‖ + ‖affine * (separation - limit)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = 4 * |circulation| * (‖center - affine‖ * ‖separation‖ + ‖affine‖ * ‖separation - limit‖) := by
      rw [norm_mul, norm_mul]
    _ ≤ 4 * |circulation| * ((scatteringBound / time) * 2 +
        ((frequency + ‖offset‖) * time) * (scatteringBound / time ^ 2)) := by gcongr
    _ = 4 * |circulation| * (2 * scatteringBound + scatteringBound * (frequency + ‖offset‖)) / time := by
      field_simp
      ring
    _ ≤ bound / time := by
      apply div_le_div_of_nonneg_right _ timePositive.le
      dsimp [bound]
      linarith

theorem physical_separating_moment_growth (length circulation : ℝ)
    (lengthPositive : 0 < length) (circulationPositive : 0 < circulation) :
    let frequency : ℝ := circulation / (2 * Real.pi * length ^ 2)
    let frequencyPositive : 0 < frequency := by dsimp [frequency]; positivity
    ∃ angle : ℝ, ∃ momentOffset : ℂ, ∃ bound > (0 : ℝ), ∃ timeMin > (0 : ℝ),
      ∀ time, timeMin ≤ time →
      ‖quadrupoleComplexMoment circulation
          ((length : ℂ) * separatingPositive frequency frequencyPositive time)
          ((length : ℂ) * separatingNegative frequency frequencyPositive time) +
        (2 * Complex.I / (Real.pi : ℂ)) * (circulation : ℂ) ^ 2 *
          Complex.exp (2 * Complex.I * (angle : ℂ)) * (time : ℂ) - momentOffset‖ ≤ bound / time := by
  dsimp only
  have frequencyPositive : 0 < circulation / (2 * Real.pi * length ^ 2) := by positivity
  obtain ⟨angle, offset, bound, boundPositive, timeMin, timePositive, estimate⟩ :=
    separating_complex_moment_growth (circulation / (2 * Real.pi * length ^ 2)) frequencyPositive
      (circulation * length ^ 2)
  refine ⟨angle, offset, bound, boundPositive, timeMin, timePositive, ?_⟩
  intro time timeAbove
  convert estimate time timeAbove using 1
  congr 1
  have coefficientIdentity :
      4 * Complex.I * ((circulation * length ^ 2 : ℝ) : ℂ) *
        ((circulation / (2 * Real.pi * length ^ 2) : ℝ) : ℂ) =
      (2 * Complex.I / (Real.pi : ℂ)) * (circulation : ℂ) ^ 2 := by
    push_cast
    have lengthNonzero : (length : ℂ) ≠ 0 := by exact_mod_cast lengthPositive.ne'
    have piNonzero : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [lengthNonzero, piNonzero]
    ring
  rw [coefficientIdentity]
  dsimp [quadrupoleComplexMoment]
  push_cast
  ring

end EulerNonuniqueness.Section6
