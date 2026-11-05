import EulerNonuniqueness.Section3.RelabeledPrimitiveAngularDerivative
import EulerNonuniqueness.Section3.DiskForcingSeriesDerivative

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace

def relabeledPrimitiveScalarJet (degree : ℕ) (frequency : ℝ) (amplitude amplitudeDerivative : ℝ → ℂ)
    (time : ℝ) : ℂ :=
  diskForcingPrimitiveFactor degree frequency * amplitudeDerivative time * diskForcingPhase degree frequency time +
    (diskForcingPrimitiveFactor degree frequency *
      (-Complex.I * ((degree + 2 : ℕ) : ℂ) * (frequency : ℂ) / 2)) *
      amplitude time * diskForcingPhase degree frequency time

def relabeledPrimitiveMovingTermJet (degree : ℕ) (frequency : ℝ)
    (amplitude amplitudeDerivative : ℝ → ℂ) (time : ℝ) (angular baseVelocity : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  relabeledPrimitiveScalarJet degree frequency amplitude amplitudeDerivative time • relabeledDiskForcingMode angular degree +
    rotatedExteriorPowerFirstJet (Circle.exp (frequency * time / 2)) (diskRelabelCurve angular 1) degree
      (diskForcingPrimitiveFactor degree frequency * amplitude time) baseVelocity

theorem relabeledPrimitiveMovingTerm_hasDerivAt (degree : ℕ) (frequency time : ℝ)
    {amplitude : ℝ → ℂ} {amplitudeVelocity : ℂ}
    {angular : ℝ → PeriodicC1HolderHalf} {baseVelocity : PeriodicC1HolderHalf}
    (amplitudeActual : HasDerivAt amplitude amplitudeVelocity time)
    (baseActual : HasDerivAt (fun current => diskRelabelCurve (angular current) 1) baseVelocity time)
    (bounded : ‖diskRelabelCurve (angular time) 1‖ < 3) :
    HasDerivAt (fun current => relabeledDiskForcingPrimitive (angular current) degree frequency amplitude current)
      (relabeledPrimitiveMovingTermJet degree frequency amplitude (fun _ => amplitudeVelocity) time
        (angular time) baseVelocity) time := by
  have scalarActual := ((amplitudeActual.const_mul (diskForcingPrimitiveFactor degree frequency)).mul
    (diskForcingPhase_hasDerivAt degree frequency time))
  have scalarIdentity :
      diskForcingPrimitiveFactor degree frequency * amplitudeVelocity * diskForcingPhase degree frequency time +
        (diskForcingPrimitiveFactor degree frequency * amplitude time) *
          (diskForcingPhase degree frequency time *
            (-Complex.I * ((degree + 2 : ℕ) : ℂ) * (frequency : ℂ) / 2)) =
      relabeledPrimitiveScalarJet degree frequency amplitude (fun _ => amplitudeVelocity) time := by
    unfold relabeledPrimitiveScalarJet
    ring
  rw [scalarIdentity] at scalarActual
  have powerActual := (hasFDerivAt_c1NaturalPowerFirstJet (diskRelabelCurve (angular time) 1) bounded (degree + 1)).comp_hasDerivAt
    time baseActual
  have modeActual := c1ConjugateCLM.hasFDerivAt.comp_hasDerivAt time powerActual
  change HasDerivAt
    (fun current => c1Conjugate (c1NaturalPower (diskRelabelCurve (angular current) 1) (degree + 1)))
    (c1Conjugate (c1NaturalPowerFirstJet (diskRelabelCurve (angular time) 1) (degree + 1) baseVelocity)) time at modeActual
  have actual := scalarActual.smul modeActual
  convert actual using 1
  unfold relabeledPrimitiveMovingTermJet relabeledDiskForcingMode
  rw [rotatedExteriorPowerFirstJet_apply, diskForcingPhase_eq_rotation_power]
  rw [add_comm]
  congr 1
  congr 1
  ring

theorem diskForcingPrimitive_phaseDerivativeFactor_norm_le (degree : ℕ) {frequency : ℝ}
    (nonzero : frequency ≠ 0) :
    ‖diskForcingPrimitiveFactor degree frequency *
      (-Complex.I * ((degree + 2 : ℕ) : ℂ) * (frequency : ℂ) / 2)‖ ≤ 2 := by
  rw [diskForcingPrimitiveFactor_identity degree nonzero]
  have scaled : ‖(frequency : ℂ) * (-Complex.I / 2 * diskForcingPrimitiveFactor degree frequency)‖ ≤ 1 := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_div, norm_neg,
      Complex.norm_I, Complex.norm_ofNat]
    have factor := mul_le_mul_of_nonneg_left (diskForcingPrimitiveFactor_norm_le nonzero degree)
      (show 0 ≤ |frequency| * (1 / 2) by positivity)
    have cancellation : |frequency| * (1 / 2) * (2 / |frequency|) = (1 : ℝ) := by
      field_simp [abs_ne_zero.mpr nonzero]
    calc
      _ = |frequency| * (1 / 2) * ‖diskForcingPrimitiveFactor degree frequency‖ := by ring
      _ ≤ |frequency| * (1 / 2) * (2 / |frequency|) := factor
      _ = 1 := cancellation
  exact (norm_add_le _ _).trans (by rw [norm_one]; linarith)

theorem relabeledPrimitiveScalarJet_norm_le (degree : ℕ) {frequency : ℝ} (nonzero : frequency ≠ 0)
    (amplitude amplitudeDerivative : ℝ → ℂ) (time : ℝ) :
    ‖relabeledPrimitiveScalarJet degree frequency amplitude amplitudeDerivative time‖ ≤
      (2 / |frequency|) * ‖amplitudeDerivative time‖ + 2 * ‖amplitude time‖ := by
  unfold relabeledPrimitiveScalarJet
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_mul, norm_mul, diskForcingPhase_norm, mul_one]
    exact mul_le_mul_of_nonneg_right (diskForcingPrimitiveFactor_norm_le nonzero degree) (norm_nonneg _)
  · rw [norm_mul, norm_mul, diskForcingPhase_norm, mul_one]
    exact mul_le_mul_of_nonneg_right (diskForcingPrimitive_phaseDerivativeFactor_norm_le degree nonzero) (norm_nonneg _)

theorem relabeledPrimitiveMovingTermJet_norm_le (degree : ℕ) {frequency : ℝ} (nonzero : frequency ≠ 0)
    (amplitude amplitudeDerivative : ℝ → ℂ) (time : ℝ) (angular baseVelocity : PeriodicC1HolderHalf)
    (bounded : ‖diskRelabelCurve angular 1‖ ≤ 3) :
    ‖relabeledPrimitiveMovingTermJet degree frequency amplitude amplitudeDerivative time angular baseVelocity‖ ≤
      ((2 / |frequency|) * ‖amplitudeDerivative time‖ +
        (2 + (2 / |frequency|) * ‖baseVelocity‖) * ‖amplitude time‖) * (48 : ℝ) ^ (degree + 1) := by
  have modeBound : ‖relabeledDiskForcingMode angular degree‖ ≤ (24 : ℝ) ^ (degree + 1) := by
    have actual := rotatedExteriorPower_norm_bound (1 : Circle) (diskRelabelCurve angular 1) bounded degree 1
    simpa only [rotatedExteriorPower, OneMemClass.coe_one, inv_one, one_pow, mul_one, one_smul,
      norm_one, relabeledDiskForcingMode] using actual
  have mode48 := modeBound.trans (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 24) (by norm_num : (24 : ℝ) ≤ 48) _)
  have jet := (rotatedExteriorPowerFirstJet (Circle.exp (frequency * time / 2)) (diskRelabelCurve angular 1) degree
    (diskForcingPrimitiveFactor degree frequency * amplitude time)).le_opNorm baseVelocity
  have operator := rotatedExteriorPowerFirstJet_norm_bound (Circle.exp (frequency * time / 2))
    (diskRelabelCurve angular 1) bounded degree (diskForcingPrimitiveFactor degree frequency * amplitude time)
  have coefficient : ‖diskForcingPrimitiveFactor degree frequency * amplitude time‖ ≤
      (2 / |frequency|) * ‖amplitude time‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (diskForcingPrimitiveFactor_norm_le nonzero degree) (norm_nonneg _)
  have operator48 := operator.trans (mul_le_mul
    (le_refl ((48 : ℝ) ^ (degree + 1))) coefficient
    (norm_nonneg _) (by positivity))
  have angularBound := jet.trans (mul_le_mul_of_nonneg_right operator48 (norm_nonneg _))
  unfold relabeledPrimitiveMovingTermJet
  apply (norm_add_le _ _).trans
  rw [norm_smul]
  exact (add_le_add
    (mul_le_mul (relabeledPrimitiveScalarJet_norm_le degree nonzero amplitude amplitudeDerivative time) mode48
      (norm_nonneg _) (by positivity)) angularBound).trans_eq (by ring)

end EulerNonuniqueness.Paper
