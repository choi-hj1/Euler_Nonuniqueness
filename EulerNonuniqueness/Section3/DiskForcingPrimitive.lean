import EulerNonuniqueness.Section3.DiskForcingModes

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

def diskForcingPhase (degree : ℕ) (frequency time : ℝ) : ℂ :=
  Complex.exp ((-Complex.I * ((degree + 2 : ℕ) : ℂ) * (frequency : ℂ) / 2) * (time : ℂ))

def diskForcingPrimitiveFactor (degree : ℕ) (frequency : ℝ) : ℂ :=
  2 * Complex.I / (((degree + 1 : ℕ) : ℂ) * (frequency : ℂ))

def diskForcingPrimitive (degree : ℕ) (frequency : ℝ) (amplitude : ℝ → ℂ)
    (time : ℝ) : PeriodicC1HolderHalf :=
  (diskForcingPrimitiveFactor degree frequency * amplitude time * diskForcingPhase degree frequency time) •
    c1Conjugate (diskCircleMode (degree + 1))

theorem diskForcingPhase_norm (degree : ℕ) (frequency time : ℝ) :
    ‖diskForcingPhase degree frequency time‖ = 1 := by
  unfold diskForcingPhase
  rw [Complex.norm_exp]
  simp

theorem diskForcingPrimitiveFactor_norm (degree : ℕ) (frequency : ℝ) :
    ‖diskForcingPrimitiveFactor degree frequency‖ =
      2 / (((degree + 1 : ℕ) : ℝ) * |frequency|) := by
  simp only [diskForcingPrimitiveFactor, norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_I,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, mul_one]

theorem diskForcingPrimitive_norm (degree : ℕ) (frequency : ℝ) (amplitude : ℝ → ℂ) (time : ℝ) :
    ‖diskForcingPrimitive degree frequency amplitude time‖ =
      (2 / (((degree + 1 : ℕ) : ℝ) * |frequency|)) * ‖amplitude time‖ *
        ‖c1Conjugate (diskCircleMode (degree + 1))‖ := by
  unfold diskForcingPrimitive
  rw [norm_smul (diskForcingPrimitiveFactor degree frequency * amplitude time * diskForcingPhase degree frequency time)
    (c1Conjugate (diskCircleMode (degree + 1))), norm_mul, norm_mul,
    diskForcingPhase_norm, mul_one, diskForcingPrimitiveFactor_norm]

theorem diskForcingPhase_hasDerivAt (degree : ℕ) (frequency time : ℝ) :
    HasDerivAt (diskForcingPhase degree frequency)
      (diskForcingPhase degree frequency time *
        (-Complex.I * ((degree + 2 : ℕ) : ℂ) * (frequency : ℂ) / 2)) time := by
  have realJet : HasDerivAt (fun current : ℝ => (current : ℂ)) 1 time := Complex.ofRealCLM.hasDerivAt
  simpa only [mul_one] using (realJet.const_mul
    (-Complex.I * ((degree + 2 : ℕ) : ℂ) * (frequency : ℂ) / 2)).cexp

theorem diskForcingPrimitiveFactor_identity (degree : ℕ) {frequency : ℝ} (nonzero : frequency ≠ 0) :
    diskForcingPrimitiveFactor degree frequency *
      (-Complex.I * ((degree + 2 : ℕ) : ℂ) * (frequency : ℂ) / 2) =
      (frequency : ℂ) * (-Complex.I / 2 * diskForcingPrimitiveFactor degree frequency) + 1 := by
  have frequencyNonzero : (frequency : ℂ) ≠ 0 := by exact_mod_cast nonzero
  have degreeNonzero : ((degree + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero degree
  have cancellation : diskForcingPrimitiveFactor degree frequency *
      (((degree + 1 : ℕ) : ℂ) * (frequency : ℂ)) = 2 * Complex.I :=
    div_mul_cancel₀ _ (mul_ne_zero degreeNonzero frequencyNonzero)
  have degreeIdentity : ((degree + 2 : ℕ) : ℂ) = ((degree + 1 : ℕ) : ℂ) + 1 := by push_cast; ring
  rw [degreeIdentity]
  calc
    _ = (frequency : ℂ) * (-Complex.I / 2 * diskForcingPrimitiveFactor degree frequency) +
        (-Complex.I / 2) * (diskForcingPrimitiveFactor degree frequency *
          (((degree + 1 : ℕ) : ℂ) * (frequency : ℂ))) := by ring
    _ = _ := by
      rw [cancellation]
      have imaginary : (-Complex.I / 2) * (2 * Complex.I) = 1 := by
        calc
          _ = -(Complex.I ^ 2) := by ring
          _ = 1 := by rw [Complex.I_sq]; norm_num
      rw [imaginary]

theorem diskForcingPrimitive_hasDerivAt (degree : ℕ) {frequency time : ℝ}
    (nonzero : frequency ≠ 0) {amplitude : ℝ → ℂ} {amplitudeDerivative : ℂ}
    (amplitudeEquation : HasDerivAt amplitude amplitudeDerivative time) :
    HasDerivAt (diskForcingPrimitive degree frequency amplitude)
      (frequency • diskRotatingDerivative (diskForcingPrimitive degree frequency amplitude time) +
        (amplitude time * diskForcingPhase degree frequency time) •
          c1Conjugate (diskCircleMode (degree + 1)) +
        (diskForcingPrimitiveFactor degree frequency * amplitudeDerivative *
          diskForcingPhase degree frequency time) • c1Conjugate (diskCircleMode (degree + 1))) time := by
  have scalarEquation := ((amplitudeEquation.const_mul (diskForcingPrimitiveFactor degree frequency)).mul
    (diskForcingPhase_hasDerivAt degree frequency time)).smul_const
      (c1Conjugate (diskCircleMode (degree + 1)))
  apply scalarEquation.congr_deriv
  rw [diskForcingPrimitive, diskRotatingDerivative_forcing_mode]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change
    ((diskForcingPrimitiveFactor degree frequency * amplitudeDerivative) * diskForcingPhase degree frequency time +
      (diskForcingPrimitiveFactor degree frequency * amplitude time) *
        (diskForcingPhase degree frequency time * (-Complex.I * ((degree + 2 : ℕ) : ℂ) * (frequency : ℂ) / 2))) *
      star ((diskCircleMode (degree + 1)).val.1 label) =
    (frequency : ℂ) * ((-Complex.I / 2 *
      (diskForcingPrimitiveFactor degree frequency * amplitude time * diskForcingPhase degree frequency time)) *
        star ((diskCircleMode (degree + 1)).val.1 label)) +
      (amplitude time * diskForcingPhase degree frequency time) * star ((diskCircleMode (degree + 1)).val.1 label) +
      (diskForcingPrimitiveFactor degree frequency * amplitudeDerivative * diskForcingPhase degree frequency time) *
        star ((diskCircleMode (degree + 1)).val.1 label)
  have scalarIdentity :
      (diskForcingPrimitiveFactor degree frequency * amplitudeDerivative) * diskForcingPhase degree frequency time +
        (diskForcingPrimitiveFactor degree frequency * amplitude time) *
          (diskForcingPhase degree frequency time * (-Complex.I * ((degree + 2 : ℕ) : ℂ) * (frequency : ℂ) / 2)) =
      (frequency : ℂ) * (-Complex.I / 2 * (diskForcingPrimitiveFactor degree frequency * amplitude time *
        diskForcingPhase degree frequency time)) + amplitude time * diskForcingPhase degree frequency time +
        diskForcingPrimitiveFactor degree frequency * amplitudeDerivative * diskForcingPhase degree frequency time := by
    calc
      _ = diskForcingPrimitiveFactor degree frequency * amplitudeDerivative * diskForcingPhase degree frequency time +
          (amplitude time * diskForcingPhase degree frequency time) *
            (diskForcingPrimitiveFactor degree frequency *
              (-Complex.I * ((degree + 2 : ℕ) : ℂ) * (frequency : ℂ) / 2)) := by ring
      _ = _ := by rw [diskForcingPrimitiveFactor_identity degree nonzero]; ring
  rw [scalarIdentity]
  ring

end

end EulerNonuniqueness.Paper
