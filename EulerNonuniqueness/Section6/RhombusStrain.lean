import EulerNonuniqueness.Section6.PointShapeCoordinates
import EulerNonuniqueness.Section6.IdealGrowingResponse

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

theorem conjugate_ratio_rotated_radius {radius : ℝ} (radiusNonzero : radius ≠ 0) (phase : ℝ) :
    star ((radius : ℂ) * Complex.exp (Complex.I * (phase : ℂ))) /
      ((radius : ℂ) * Complex.exp (Complex.I * (phase : ℂ))) =
        Complex.exp (-2 * Complex.I * (phase : ℂ)) := by
  have radiusComplexNonzero : (radius : ℂ) ≠ 0 := by exact_mod_cast radiusNonzero
  simp only [star_mul, Complex.star_def, map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.conj_I]
  rw [mul_comm (Complex.exp (-Complex.I * (phase : ℂ))) (radius : ℂ),
    mul_div_mul_left _ _ radiusComplexNonzero, ← Complex.exp_sub]
  congr 1
  ring

theorem strain_logarithmic_velocity_rotating_receiver {radius : ℝ} (radiusNonzero : radius ≠ 0)
    (frequency strainAmplitude phase receiverPhase time : ℝ) :
    let positive := (radius : ℂ) * Complex.exp (Complex.I * ((receiverPhase - frequency * time : ℝ) : ℂ))
    let strain := ((strainAmplitude * time : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((phase + 2 * receiverPhase : ℝ) : ℂ))
    strain * star positive / positive = ((strainAmplitude * time : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((phase + 2 * frequency * time : ℝ) : ℂ)) := by
  dsimp only
  rw [mul_div_assoc, conjugate_ratio_rotated_radius radiusNonzero, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem rotating_rhombus_strain_unstable_input {radius : ℝ} (radiusNonzero : radius ≠ 0)
    (frequency strainAmplitude phase receiverPhase time : ℝ) :
    let positive := (radius : ℂ) * Complex.exp (Complex.I * ((receiverPhase - frequency * time : ℝ) : ℂ))
    let negative := Complex.I * (Real.sqrt rhombusRatio : ℂ) * positive
    let strain := ((strainAmplitude * time : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((phase + 2 * receiverPhase : ℝ) : ℂ))
    (pointShapeForcing positive negative (strain * star positive) (strain * star negative)).1 =
      idealStrainInput frequency strainAmplitude phase time := by
  dsimp only
  have positiveNonzero : (radius : ℂ) *
      Complex.exp (Complex.I * ((receiverPhase - frequency * time : ℝ) : ℂ)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast radiusNonzero) (Complex.exp_ne_zero _)
  rw [pointShapeForcing_rhombus positiveNonzero]
  dsimp only
  rw [strain_logarithmic_velocity_rotating_receiver radiusNonzero]
  simp [idealStrainInput, Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]

def leadingSourceStrain (circulation distance bearing outgoingPhase time : ℝ) : ℂ :=
  ((3 * circulation ^ 2 / (Real.pi ^ 2 * distance ^ 4) * time : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((4 * bearing - 2 * outgoingPhase : ℝ) : ℂ))

def rotatingRhombusGrowingStrainInput
    (radius frequency circulation distance bearing receiverPhase outgoingPhase time : ℝ) : ℝ :=
  let positive := (radius : ℂ) * Complex.exp (Complex.I * ((receiverPhase - frequency * time : ℝ) : ℂ))
  let negative := Complex.I * (Real.sqrt rhombusRatio : ℂ) * positive
  let strain := leadingSourceStrain circulation distance bearing outgoingPhase time
  (pointShapeForcing positive negative (strain * star positive) (strain * star negative)).1

theorem idealStrainInput_weighted_integrable (frequency strainAmplitude phase : ℝ)
    (frequencyPositive : 0 < frequency) :
    MeasureTheory.IntegrableOn (fun time => Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
      idealStrainInput frequency strainAmplitude phase time) (Set.Ioi 0) := by
  let offset := phase + Real.arctan (1 / Real.sqrt 2) - Real.pi
  let coefficient := strainAmplitude * Real.sqrt 2 / (4 * Real.sqrt 3 * frequency ^ 2)
  have phaseIdentity : Real.pi - Real.arctan (1 / Real.sqrt 2) + offset = phase := by
    dsimp [offset]
    ring
  have integrable := ((idealGrowingInput_weighted_integrable frequency coefficient frequencyPositive).const_mul
    (Real.cos offset)).add ((idealQuadratureInput_weighted_integrable frequency coefficient frequencyPositive).const_mul
      (Real.sin offset))
  have integrandIdentity :
      (fun time => Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
        idealStrainInput frequency strainAmplitude phase time) =
      ((fun time => Real.cos offset * (Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
        idealGrowingInput frequency coefficient time)) +
        (fun time => Real.sin offset * (Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
          idealQuadratureInput frequency coefficient time))) := by
    funext time
    rw [← phaseIdentity, idealStrainInput_phase_decomposition _ _ _ _ frequencyPositive.ne']
    dsimp [coefficient]
    ring
  rw [integrandIdentity]
  exact integrable

theorem rotatingRhombusGrowingStrainInput_eq {radius : ℝ} (radiusNonzero : radius ≠ 0)
    (frequency circulation distance bearing receiverPhase outgoingPhase time : ℝ) :
    rotatingRhombusGrowingStrainInput radius frequency circulation distance bearing receiverPhase outgoingPhase time =
      idealStrainInput frequency (3 * circulation ^ 2 / (Real.pi ^ 2 * distance ^ 4))
        (4 * bearing - 2 * receiverPhase - 2 * outgoingPhase) time := by
  have identity : 4 * bearing - 2 * receiverPhase - 2 * outgoingPhase + 2 * receiverPhase =
      4 * bearing - 2 * outgoingPhase := by ring
  have result := rotating_rhombus_strain_unstable_input radiusNonzero frequency
    (3 * circulation ^ 2 / (Real.pi ^ 2 * distance ^ 4))
    (4 * bearing - 2 * receiverPhase - 2 * outgoingPhase) receiverPhase time
  dsimp only at result
  rw [identity] at result
  exact result

theorem rotating_rhombus_source_positive_coefficient {radius : ℝ} (radiusNonzero : radius ≠ 0)
    (frequency circulation distance bearing receiverPhase outgoingPhase : ℝ)
    (frequencyPositive : 0 < frequency) (distancePositive : 0 < distance) :
    (∫ time : ℝ in Set.Ioi 0, Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
      rotatingRhombusGrowingStrainInput radius frequency circulation distance bearing receiverPhase outgoingPhase time) =
      Real.sqrt 3 * circulation ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * frequency ^ 2 * distance ^ 4) *
        Real.cos (4 * bearing - 2 * receiverPhase - 2 * outgoingPhase +
          Real.arctan (1 / Real.sqrt 2) - Real.pi) := by
  simp_rw [rotatingRhombusGrowingStrainInput_eq radiusNonzero]
  exact ideal_strain_source_coefficient frequency circulation distance
    (4 * bearing - 2 * receiverPhase - 2 * outgoingPhase) frequencyPositive distancePositive

theorem rotatingRhombusGrowingStrainInput_weighted_integrable {radius : ℝ} (radiusNonzero : radius ≠ 0)
    (frequency circulation distance bearing receiverPhase outgoingPhase : ℝ)
    (frequencyPositive : 0 < frequency) :
    MeasureTheory.IntegrableOn (fun time => Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
      rotatingRhombusGrowingStrainInput radius frequency circulation distance bearing receiverPhase outgoingPhase time)
      (Set.Ioi 0) := by
  simp_rw [rotatingRhombusGrowingStrainInput_eq radiusNonzero]
  exact idealStrainInput_weighted_integrable _ _ _ frequencyPositive

theorem rotating_rhombus_maximizing_strain_positive {radius : ℝ} (radiusNonzero : radius ≠ 0)
    (frequency circulation distance bearing receiverPhase outgoingPhase : ℝ)
    (frequencyPositive : 0 < frequency) (distancePositive : 0 < distance) (circulationNonzero : circulation ≠ 0)
    (phaseAlignment : 4 * bearing - 2 * receiverPhase - 2 * outgoingPhase =
      Real.pi - Real.arctan (1 / Real.sqrt 2)) :
    0 < ∫ time : ℝ in Set.Ioi 0, Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
      rotatingRhombusGrowingStrainInput radius frequency circulation distance bearing receiverPhase outgoingPhase time := by
  rw [rotating_rhombus_source_positive_coefficient radiusNonzero _ _ _ _ _ _ frequencyPositive distancePositive,
    phaseAlignment]
  have argumentZero : Real.pi - Real.arctan (1 / Real.sqrt 2) +
      Real.arctan (1 / Real.sqrt 2) - Real.pi = 0 := by ring
  rw [argumentZero, Real.cos_zero, mul_one]
  have circulationSquarePositive := sq_pos_of_ne_zero circulationNonzero
  positivity

end EulerNonuniqueness.Section6
