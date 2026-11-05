import EulerNonuniqueness.Section2.PointVortices
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Proposition 2.1: the actual complex rotating rhombus

The positions are exactly the manuscript's equation `eq:rhombus`.
`proposition21` proves both complex equations `eq:point-ode` for every real
time, together with positive frequency, the prescribed impulse, and all
noncollision conditions. No dynamical existence theorem is assumed.
-/

noncomputable section

namespace EulerNonuniqueness.Section2

def rhombusFrequency (length circulation : ℝ) : ℝ :=
  circulation / (2 * Real.pi * length ^ 2)

def rhombusPositiveAmplitude (length : ℝ) : ℝ :=
  length * Real.sqrt ((Real.sqrt 2 + 1) / 2)

def rhombusNegativeAmplitude (length : ℝ) : ℝ :=
  length * Real.sqrt ((Real.sqrt 2 - 1) / 2)

def rhombusRotation (frequency initialPhase time : ℝ) : ℂ :=
  Complex.exp (Complex.I * (initialPhase - frequency * time : ℝ))

def rhombusPositive (length circulation initialPhase time : ℝ) : ℂ :=
  (rhombusPositiveAmplitude length : ℂ) *
    rhombusRotation (rhombusFrequency length circulation) initialPhase time

def rhombusNegative (length circulation initialPhase time : ℝ) : ℂ :=
  Complex.I * (rhombusNegativeAmplitude length : ℂ) *
    rhombusRotation (rhombusFrequency length circulation) initialPhase time

theorem rhombus_amplitude_squares (length : ℝ) :
    rhombusPositiveAmplitude length ^ 2 = length ^ 2 * ((Real.sqrt 2 + 1) / 2) ∧
    rhombusNegativeAmplitude length ^ 2 = length ^ 2 * ((Real.sqrt 2 - 1) / 2) := by
  constructor
  · unfold rhombusPositiveAmplitude
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  · unfold rhombusNegativeAmplitude
    rw [mul_pow, Real.sq_sqrt (by linarith [sqrt_two_gt_one])]

theorem rhombus_amplitudes_pos {length : ℝ} (lengthPositive : 0 < length) :
    0 < rhombusPositiveAmplitude length ∧ 0 < rhombusNegativeAmplitude length := by
  constructor
  · exact mul_pos lengthPositive (Real.sqrt_pos.2 (by positivity))
  · exact mul_pos lengthPositive (Real.sqrt_pos.2 (by linarith [sqrt_two_gt_one]))

theorem rhombusRotation_norm (frequency initialPhase time : ℝ) :
    ‖rhombusRotation frequency initialPhase time‖ = 1 := by
  simp [rhombusRotation, Complex.norm_exp]

theorem rhombusRotation_star (frequency initialPhase time : ℝ) :
    star (rhombusRotation frequency initialPhase time) =
      (rhombusRotation frequency initialPhase time)⁻¹ := by
  have product : star (rhombusRotation frequency initialPhase time) *
      rhombusRotation frequency initialPhase time = 1 := by
    simpa [Complex.star_def, rhombusRotation_norm] using
      Complex.conj_mul' (rhombusRotation frequency initialPhase time)
  exact eq_inv_of_mul_eq_one_left product

theorem rhombusRotation_hasDerivAt (frequency initialPhase time : ℝ) :
    HasDerivAt (rhombusRotation frequency initialPhase)
      (-Complex.I * (frequency : ℂ) * rhombusRotation frequency initialPhase time) time := by
  have phaseDerivative := ((hasDerivAt_const time initialPhase).sub
    ((hasDerivAt_id time).const_mul frequency)).ofReal_comp
  have exponentialDerivative := (phaseDerivative.const_mul Complex.I).cexp
  convert exponentialDerivative using 1
  simp only [rhombusRotation, Complex.ofReal_sub,
    Complex.ofReal_zero, Complex.ofReal_mul, Complex.ofReal_one, sub_zero, mul_one, id_eq]
  ring

theorem rotating_rhombus_impulse (length circulation initialPhase time : ℝ) :
    ‖rhombusPositive length circulation initialPhase time‖ ^ 2 -
      ‖rhombusNegative length circulation initialPhase time‖ ^ 2 = length ^ 2 := by
  simp only [rhombusPositive, rhombusNegative, norm_mul, Complex.norm_I,
    one_mul, rhombusRotation_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [(rhombus_amplitude_squares length).1, (rhombus_amplitude_squares length).2]
  ring

theorem rhombus_amplitude_balances (length : ℝ) :
    2 * rhombusPositiveAmplitude length ^ 2 *
      (rhombusPositiveAmplitude length ^ 2 + rhombusNegativeAmplitude length ^ 2) =
        length ^ 2 * (3 * rhombusPositiveAmplitude length ^ 2 -
          rhombusNegativeAmplitude length ^ 2) ∧
    2 * rhombusNegativeAmplitude length ^ 2 *
      (rhombusPositiveAmplitude length ^ 2 + rhombusNegativeAmplitude length ^ 2) =
        length ^ 2 * (rhombusPositiveAmplitude length ^ 2 -
          3 * rhombusNegativeAmplitude length ^ 2) := by
  rw [(rhombus_amplitude_squares length).1, (rhombus_amplitude_squares length).2]
  constructor <;> ring_nf <;> norm_num [Real.sq_sqrt] <;> ring

theorem rotating_rhombus_noncollision (length circulation initialPhase time : ℝ)
    (lengthPositive : 0 < length) :
    rhombusPositive length circulation initialPhase time ≠ 0 ∧
    rhombusNegative length circulation initialPhase time ≠ 0 ∧
    rhombusPositive length circulation initialPhase time -
      rhombusNegative length circulation initialPhase time ≠ 0 ∧
    rhombusPositive length circulation initialPhase time +
      rhombusNegative length circulation initialPhase time ≠ 0 := by
  have positiveAmplitude := (rhombus_amplitudes_pos lengthPositive).1
  have negativeAmplitude := (rhombus_amplitudes_pos lengthPositive).2
  have rotationNonzero : rhombusRotation (rhombusFrequency length circulation)
      initialPhase time ≠ 0 := Complex.exp_ne_zero _
  refine ⟨mul_ne_zero (Complex.ofReal_ne_zero.mpr positiveAmplitude.ne') rotationNonzero,
    mul_ne_zero (mul_ne_zero Complex.I_ne_zero
      (Complex.ofReal_ne_zero.mpr negativeAmplitude.ne')) rotationNonzero, ?_, ?_⟩
  · intro equality
    have impulse := rotating_rhombus_impulse length circulation initialPhase time
    rw [sub_eq_zero.mp equality, sub_self] at impulse
    nlinarith
  · intro equality
    have impulse := rotating_rhombus_impulse length circulation initialPhase time
    rw [eq_neg_of_add_eq_zero_left equality, norm_neg, sub_self] at impulse
    nlinarith

theorem rotating_rhombus_velocity_identities (length circulation initialPhase time : ℝ)
    (lengthPositive : 0 < length) :
    -Complex.I * (circulation : ℂ) *
      (3 * star (rhombusPositive length circulation initialPhase time) ^ 2 +
        star (rhombusNegative length circulation initialPhase time) ^ 2) /
      (4 * (Real.pi : ℂ) * star (rhombusPositive length circulation initialPhase time) *
        (star (rhombusPositive length circulation initialPhase time) ^ 2 -
          star (rhombusNegative length circulation initialPhase time) ^ 2)) =
      -Complex.I * (rhombusFrequency length circulation : ℂ) *
        rhombusPositive length circulation initialPhase time ∧
    -Complex.I * (circulation : ℂ) *
      (star (rhombusPositive length circulation initialPhase time) ^ 2 +
        3 * star (rhombusNegative length circulation initialPhase time) ^ 2) /
      (4 * (Real.pi : ℂ) * star (rhombusNegative length circulation initialPhase time) *
        (star (rhombusPositive length circulation initialPhase time) ^ 2 -
          star (rhombusNegative length circulation initialPhase time) ^ 2)) =
      -Complex.I * (rhombusFrequency length circulation : ℂ) *
        rhombusNegative length circulation initialPhase time := by
  let positive : ℂ := rhombusPositiveAmplitude length
  let negative : ℂ := rhombusNegativeAmplitude length
  let rotation := rhombusRotation (rhombusFrequency length circulation) initialPhase time
  have positiveNonzero : positive ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (rhombus_amplitudes_pos lengthPositive).1.ne'
  have negativeNonzero : negative ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (rhombus_amplitudes_pos lengthPositive).2.ne'
  have rotationNonzero : rotation ≠ 0 := Complex.exp_ne_zero _
  have lengthNonzero : (length : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr lengthPositive.ne'
  have piNonzero : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have sumNonzero : positive ^ 2 + negative ^ 2 ≠ 0 := by
    dsimp [positive, negative]
    norm_cast
    have positiveSquare := sq_pos_of_pos (rhombus_amplitudes_pos lengthPositive).1
    nlinarith [sq_nonneg (rhombusNegativeAmplitude length)]
  have firstBalance : 2 * positive ^ 2 * (positive ^ 2 + negative ^ 2) =
      (length : ℂ) ^ 2 * (3 * positive ^ 2 - negative ^ 2) := by
    dsimp [positive, negative]
    exact_mod_cast (rhombus_amplitude_balances length).1
  have secondBalance : 2 * negative ^ 2 * (positive ^ 2 + negative ^ 2) =
      (length : ℂ) ^ 2 * (positive ^ 2 - 3 * negative ^ 2) := by
    dsimp [positive, negative]
    exact_mod_cast (rhombus_amplitude_balances length).2
  have starPositive : star (rhombusPositive length circulation initialPhase time) =
      positive * rotation⁻¹ := by
    simp [rhombusPositive, positive, rotation, star_mul, rhombusRotation_star, mul_comm]
  have starNegative : star (rhombusNegative length circulation initialPhase time) =
      -Complex.I * negative * rotation⁻¹ := by
    simp [rhombusNegative, negative, rotation, star_mul, rhombusRotation_star,
      mul_comm, mul_left_comm, mul_assoc]
  rw [starPositive, starNegative]
  change _ = -Complex.I * (rhombusFrequency length circulation : ℂ) *
    (positive * rotation) ∧ _ = -Complex.I * (rhombusFrequency length circulation : ℂ) *
      (Complex.I * negative * rotation)
  have squareDifference : (positive * rotation⁻¹) ^ 2 -
      (-Complex.I * negative * rotation⁻¹) ^ 2 =
      (positive ^ 2 + negative ^ 2) * (rotation⁻¹) ^ 2 := by
    ring_nf
    simp [Complex.I_sq]
  rw [squareDifference]
  simp only [rhombusFrequency, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  constructor
  · apply (div_eq_iff (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) piNonzero)
        (mul_ne_zero positiveNonzero (inv_ne_zero rotationNonzero)))
      (mul_ne_zero sumNonzero (pow_ne_zero _ (inv_ne_zero rotationNonzero))))).2
    field_simp [rotationNonzero, lengthNonzero, piNonzero]
    ring_nf
    simp only [Complex.I_sq, Complex.I_pow_three]
    linear_combination -2 * Complex.I * (circulation : ℂ) * (Real.pi : ℂ) *
      rotation ^ 3 * firstBalance
  · apply (div_eq_iff (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) piNonzero)
        (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) negativeNonzero)
          (inv_ne_zero rotationNonzero)))
      (mul_ne_zero sumNonzero (pow_ne_zero _ (inv_ne_zero rotationNonzero))))).2
    field_simp [rotationNonzero, lengthNonzero, piNonzero]
    ring_nf
    simp only [Complex.I_sq, Complex.I_pow_three]
    linear_combination 2 * Complex.I * (circulation : ℂ) * (Real.pi : ℂ) *
      rotation ^ 3 * secondBalance

theorem proposition21 (length circulation initialPhase : ℝ)
    (lengthPositive : 0 < length) (circulationPositive : 0 < circulation) :
    0 < rhombusFrequency length circulation ∧ ∀ time : ℝ,
    HasDerivAt (rhombusPositive length circulation initialPhase)
      (-Complex.I * (circulation : ℂ) *
        (3 * star (rhombusPositive length circulation initialPhase time) ^ 2 +
          star (rhombusNegative length circulation initialPhase time) ^ 2) /
        (4 * (Real.pi : ℂ) * star (rhombusPositive length circulation initialPhase time) *
          (star (rhombusPositive length circulation initialPhase time) ^ 2 -
            star (rhombusNegative length circulation initialPhase time) ^ 2))) time ∧
    HasDerivAt (rhombusNegative length circulation initialPhase)
      (-Complex.I * (circulation : ℂ) *
        (star (rhombusPositive length circulation initialPhase time) ^ 2 +
          3 * star (rhombusNegative length circulation initialPhase time) ^ 2) /
        (4 * (Real.pi : ℂ) * star (rhombusNegative length circulation initialPhase time) *
          (star (rhombusPositive length circulation initialPhase time) ^ 2 -
            star (rhombusNegative length circulation initialPhase time) ^ 2))) time ∧
    ‖rhombusPositive length circulation initialPhase time‖ ^ 2 -
      ‖rhombusNegative length circulation initialPhase time‖ ^ 2 = length ^ 2 ∧
    rhombusPositive length circulation initialPhase time ≠ 0 ∧
    rhombusNegative length circulation initialPhase time ≠ 0 ∧
    rhombusPositive length circulation initialPhase time -
      rhombusNegative length circulation initialPhase time ≠ 0 ∧
    rhombusPositive length circulation initialPhase time +
      rhombusNegative length circulation initialPhase time ≠ 0 := by
  refine ⟨div_pos circulationPositive
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) (sq_pos_of_pos lengthPositive)), ?_⟩
  intro time
  refine ⟨?_, ?_, rotating_rhombus_impulse length circulation initialPhase time,
    rotating_rhombus_noncollision length circulation initialPhase time lengthPositive⟩
  · rw [(rotating_rhombus_velocity_identities length circulation initialPhase time
      lengthPositive).1]
    convert (rhombusRotation_hasDerivAt (rhombusFrequency length circulation)
      initialPhase time).const_mul (rhombusPositiveAmplitude length : ℂ) using 1
    simp only [rhombusPositive]
    ring
  · rw [(rotating_rhombus_velocity_identities length circulation initialPhase time
      lengthPositive).2]
    convert (rhombusRotation_hasDerivAt (rhombusFrequency length circulation)
      initialPhase time).const_mul (Complex.I * (rhombusNegativeAmplitude length : ℂ)) using 1
    simp only [rhombusNegative]
    ring

end EulerNonuniqueness.Section2
