import EulerNonuniqueness.Section2.SeparatingScattering
import EulerNonuniqueness.Section5.CascadeStatement

noncomputable section

open Filter
open EulerNonuniqueness.Section2

namespace EulerNonuniqueness.Paper

def separatingCandidate (timeShift rotationPhase dipoleAngle : ℝ) (offset : ℂ) : SeparatingOrbit where
  positive time := Complex.exp (Complex.I * (rotationPhase : ℂ)) *
    separatingPositive 1 (by norm_num) (time + timeShift)
  negative time := Complex.exp (Complex.I * (rotationPhase : ℂ)) *
    separatingNegative 1 (by norm_num) (time + timeShift)
  phase time := separatingPhase 1 (by norm_num) (time + timeShift) + rotationPhase
  limitingDipoleAngle := rotationPhase + dipoleAngle
  limitingPairOffset := Complex.exp (Complex.I * (rotationPhase : ℂ)) * offset -
    Complex.I * Complex.exp (Complex.I * ((rotationPhase + dipoleAngle : ℝ) : ℂ)) * (timeShift : ℂ)

theorem separatingCandidate_rotation_norm (rotationPhase : ℝ) :
    ‖Complex.exp (Complex.I * (rotationPhase : ℂ))‖ = 1 := by
  simp [Complex.norm_exp, Complex.mul_re]

theorem separatingCandidate_norms (timeShift rotationPhase dipoleAngle time : ℝ) (offset : ℂ) :
    ‖(separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time‖ =
      ‖separatingPositive 1 (by norm_num) (time + timeShift)‖ ∧
    ‖(separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time‖ =
      ‖separatingNegative 1 (by norm_num) (time + timeShift)‖ := by
  simp [separatingCandidate, norm_mul, separatingCandidate_rotation_norm]

theorem separatingCandidate_ratio (timeShift rotationPhase dipoleAngle time : ℝ) (offset : ℂ) :
    (separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time /
      (separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time =
      separatingComplexRatio (separatingScalarOrbit 1 (by norm_num) (time + timeShift)) := by
  change (Complex.exp (Complex.I * (rotationPhase : ℂ)) * separatingNegative 1 (by norm_num) (time + timeShift)) /
    (Complex.exp (Complex.I * (rotationPhase : ℂ)) * separatingPositive 1 (by norm_num) (time + timeShift)) = _
  rw [mul_div_mul_left _ _ (Complex.exp_ne_zero _), separating_position_ratio]

theorem separatingCandidate_shapes (timeShift rotationPhase dipoleAngle time : ℝ) (offset : ℂ) :
    orbitRadialShape (separatingCandidate timeShift rotationPhase dipoleAngle offset) time =
      separatingRadialShape (separatingScalarOrbit 1 (by norm_num) (time + timeShift)) ∧
    orbitAngularShape (separatingCandidate timeShift rotationPhase dipoleAngle offset) time =
      separatingAngularShape (separatingScalarOrbit 1 (by norm_num) (time + timeShift)) := by
  have norms := separatingCandidate_norms timeShift rotationPhase dipoleAngle time offset
  have bounds := separatingScalarOrbit_mem 1 (by norm_num) (time + timeShift)
  have rhombusSquare : (Real.sqrt 2 - 1) ^ 2 = rhombusRatio := by
    unfold rhombusRatio
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  constructor
  · unfold orbitRadialShape
    rw [norms.1, norms.2, separating_norm_ratio]
    simp only [separatingRadialShape, rhombusSquare]
  · unfold orbitAngularShape
    rw [separatingCandidate_ratio, separating_arg_eq_arccos bounds.1 bounds.2]
    rfl

theorem separatingCandidate_unstableStable (timeShift rotationPhase dipoleAngle time : ℝ) (offset : ℂ) :
    orbitUnstableShape (separatingCandidate timeShift rotationPhase dipoleAngle offset) time =
      separatingUnstableShape (separatingScalarOrbit 1 (by norm_num) (time + timeShift)) ∧
    orbitStableShape (separatingCandidate timeShift rotationPhase dipoleAngle offset) time =
      separatingStableShape (separatingScalarOrbit 1 (by norm_num) (time + timeShift)) := by
  have shapes := separatingCandidate_shapes timeShift rotationPhase dipoleAngle time offset
  simp only [orbitUnstableShape, orbitStableShape, separatingUnstableShape, separatingStableShape,
    shapes.1, shapes.2, and_self]

theorem rotated_point_velocity_algebra (rotation receiver first second firstCoefficient secondCoefficient : ℂ)
    (rotationNonzero : rotation ≠ 0) (receiverNonzero : receiver ≠ 0)
    (differenceNonzero : first ^ 2 - second ^ 2 ≠ 0) :
    rotation * (-Complex.I * (firstCoefficient * first ^ 2 + secondCoefficient * second ^ 2) /
      (2 * receiver * (first ^ 2 - second ^ 2))) =
      -Complex.I * (firstCoefficient * (rotation⁻¹ * first) ^ 2 + secondCoefficient * (rotation⁻¹ * second) ^ 2) /
        (2 * (rotation⁻¹ * receiver) * ((rotation⁻¹ * first) ^ 2 - (rotation⁻¹ * second) ^ 2)) := by
  rw [show firstCoefficient * (rotation⁻¹ * first) ^ 2 + secondCoefficient * (rotation⁻¹ * second) ^ 2 =
    rotation⁻¹ ^ 2 * (firstCoefficient * first ^ 2 + secondCoefficient * second ^ 2) by ring]
  rw [show (rotation⁻¹ * first) ^ 2 - (rotation⁻¹ * second) ^ 2 =
    rotation⁻¹ ^ 2 * (first ^ 2 - second ^ 2) by ring]
  generalize differenceDefinition : first ^ 2 - second ^ 2 = difference at *
  field_simp [rotationNonzero, receiverNonzero, differenceNonzero]
  <;> ring

theorem separatingCandidate_rotation_star (rotationPhase : ℝ) :
    star (Complex.exp (Complex.I * (rotationPhase : ℂ))) =
      (Complex.exp (Complex.I * (rotationPhase : ℂ)))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa only [Complex.star_def, separatingCandidate_rotation_norm, one_pow, Complex.ofReal_one] using
    Complex.conj_mul' (Complex.exp (Complex.I * (rotationPhase : ℂ)))

theorem separatingCandidate_pointEquations (timeShift rotationPhase dipoleAngle time : ℝ) (offset : ℂ) :
    HasDerivAt (separatingCandidate timeShift rotationPhase dipoleAngle offset).positive
      (-Complex.I * (3 * star ((separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time) ^ 2 +
        star ((separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time) ^ 2) /
        (2 * star ((separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time) *
          (star ((separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time) ^ 2 -
            star ((separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time) ^ 2))) time ∧
    HasDerivAt (separatingCandidate timeShift rotationPhase dipoleAngle offset).negative
      (-Complex.I * (star ((separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time) ^ 2 +
        3 * star ((separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time) ^ 2) /
        (2 * star ((separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time) *
          (star ((separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time) ^ 2 -
            star ((separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time) ^ 2))) time := by
  have pairs := separating_pair_ne_zero 1 (by norm_num) (time + timeShift)
  have differenceNonzero : star (separatingPositive 1 (by norm_num) (time + timeShift)) ^ 2 -
      star (separatingNegative 1 (by norm_num) (time + timeShift)) ^ 2 ≠ 0 := by
    rw [show star (separatingPositive 1 (by norm_num) (time + timeShift)) ^ 2 -
      star (separatingNegative 1 (by norm_num) (time + timeShift)) ^ 2 =
      star (separatingPositive 1 (by norm_num) (time + timeShift) - separatingNegative 1 (by norm_num) (time + timeShift)) *
        star (separatingPositive 1 (by norm_num) (time + timeShift) + separatingNegative 1 (by norm_num) (time + timeShift)) by
      rw [star_sub, star_add]; ring]
    exact mul_ne_zero (star_ne_zero.mpr pairs.1) (star_ne_zero.mpr pairs.2)
  have positiveDerivative := ((separatingPositive_pointEquation 1 (by norm_num) (time + timeShift)).scomp time
    ((hasDerivAt_id time).add_const timeShift)).const_mul (Complex.exp (Complex.I * (rotationPhase : ℂ)))
  have negativeDerivative := ((separatingNegative_pointEquation 1 (by norm_num) (time + timeShift)).scomp time
    ((hasDerivAt_id time).add_const timeShift)).const_mul (Complex.exp (Complex.I * (rotationPhase : ℂ)))
  simp only [Complex.ofReal_one, mul_one, one_smul] at positiveDerivative negativeDerivative
  have positiveAlgebra := rotated_point_velocity_algebra
    (Complex.exp (Complex.I * (rotationPhase : ℂ)))
    (star (separatingPositive 1 (by norm_num) (time + timeShift)))
    (star (separatingPositive 1 (by norm_num) (time + timeShift)))
    (star (separatingNegative 1 (by norm_num) (time + timeShift))) 3 1
    (Complex.exp_ne_zero _) (star_ne_zero.mpr (separatingPositive_ne_zero 1 (by norm_num) _)) differenceNonzero
  have negativeAlgebra := rotated_point_velocity_algebra
    (Complex.exp (Complex.I * (rotationPhase : ℂ)))
    (star (separatingNegative 1 (by norm_num) (time + timeShift)))
    (star (separatingPositive 1 (by norm_num) (time + timeShift)))
    (star (separatingNegative 1 (by norm_num) (time + timeShift))) 1 3
    (Complex.exp_ne_zero _) (star_ne_zero.mpr (separatingNegative_ne_zero 1 (by norm_num) _)) differenceNonzero
  simp only [one_mul] at positiveAlgebra negativeAlgebra
  rw [positiveAlgebra] at positiveDerivative
  rw [negativeAlgebra] at negativeDerivative
  constructor
  · convert positiveDerivative using 1
    simp only [separatingCandidate, star_mul, separatingCandidate_rotation_star]
    congr 2 <;> ring
  · convert negativeDerivative using 1
    simp only [separatingCandidate, star_mul, separatingCandidate_rotation_star]
    congr 2 <;> ring

theorem separatingCandidate_geometry (timeShift rotationPhase dipoleAngle : ℝ) (offset : ℂ) :
    Continuous (separatingCandidate timeShift rotationPhase dipoleAngle offset).phase ∧
    (∀ time, ‖(separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time‖ ^ 2 -
        ‖(separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time‖ ^ 2 = 1 ∧
      (separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time =
        (‖(separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time‖ : ℂ) *
          Complex.exp (Complex.I * ((separatingCandidate timeShift rotationPhase dipoleAngle offset).phase time : ℂ))) ∧
    ∃ minimum > (0 : ℝ), ∀ time,
      minimum ≤ 2 * ‖(separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time‖ ∧
      minimum ≤ 2 * ‖(separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time‖ ∧
      minimum ≤ ‖(separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time -
        (separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time‖ ∧
      minimum ≤ ‖(separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time +
        (separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time‖ := by
  have rawContinuous : Continuous (separatingPhase 1 (by norm_num)) :=
    continuous_iff_continuousAt.mpr (fun time => (separatingPhase_hasDerivAt 1 (by norm_num) time).continuousAt)
  refine ⟨(rawContinuous.comp (continuous_id.add continuous_const)).add continuous_const, ?_, ?_⟩
  · intro time
    have norms := separatingCandidate_norms timeShift rotationPhase dipoleAngle time offset
    constructor
    · rw [norms.1, norms.2]
      exact separating_impulse 1 (by norm_num) (time + timeShift)
    · rw [norms.1, separatingPositive_norm]
      change Complex.exp (Complex.I * (rotationPhase : ℂ)) *
        (((Real.sqrt (1 - separatingScalarOrbit 1 (by norm_num) (time + timeShift) ^ 2))⁻¹ : ℝ) *
          Complex.exp (Complex.I * (separatingPhase 1 (by norm_num) (time + timeShift) : ℂ))) = _
      change _ = ((Real.sqrt (1 - separatingScalarOrbit 1 (by norm_num) (time + timeShift) ^ 2))⁻¹ : ℝ) *
        Complex.exp (Complex.I * ((separatingPhase 1 (by norm_num) (time + timeShift) + rotationPhase : ℝ) : ℂ))
      push_cast
      rw [mul_add, Complex.exp_add]
      ring
  · obtain ⟨minimum, minimumPositive, minimumProperty⟩ := separating_uniform_noncollision 1 (by norm_num)
    refine ⟨minimum, minimumPositive, ?_⟩
    intro time
    have norms := separatingCandidate_norms timeShift rotationPhase dipoleAngle time offset
    have differenceNorm : ‖(separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time -
        (separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time‖ =
        ‖separatingPositive 1 (by norm_num) (time + timeShift) - separatingNegative 1 (by norm_num) (time + timeShift)‖ := by
      change ‖Complex.exp (Complex.I * (rotationPhase : ℂ)) * _ - Complex.exp (Complex.I * (rotationPhase : ℂ)) * _‖ = _
      rw [← mul_sub, norm_mul, separatingCandidate_rotation_norm, one_mul]
    have sumNorm : ‖(separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time +
        (separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time‖ =
        ‖separatingPositive 1 (by norm_num) (time + timeShift) + separatingNegative 1 (by norm_num) (time + timeShift)‖ := by
      change ‖Complex.exp (Complex.I * (rotationPhase : ℂ)) * _ + Complex.exp (Complex.I * (rotationPhase : ℂ)) * _‖ = _
      rw [← mul_add, norm_mul, separatingCandidate_rotation_norm, one_mul]
    rw [norms.1, norms.2, differenceNorm, sumNorm]
    exact minimumProperty (time + timeShift)

theorem separatingCandidate_scattering (timeShift rotationPhase dipoleAngle : ℝ) (offset : ℂ)
    {bound timeMin : ℝ} (boundPositive : 0 < bound) (timePositive : 0 < timeMin)
    (rawError : ∀ time, timeMin ≤ time →
      ‖separatingPositive 1 (by norm_num) time + separatingNegative 1 (by norm_num) time -
        Complex.exp (Complex.I * (dipoleAngle : ℂ))‖ ≤ bound / time ^ 2 ∧
      ‖(separatingPositive 1 (by norm_num) time - separatingNegative 1 (by norm_num) time) / 2 +
        Complex.I * Complex.exp (Complex.I * (dipoleAngle : ℂ)) * (time : ℂ) - offset‖ ≤ bound / time) :
    ∃ constant > (0 : ℝ), ∃ threshold > (0 : ℝ), ∀ time, threshold ≤ time →
      ‖(separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time +
        (separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time -
        Complex.exp (Complex.I * ((separatingCandidate timeShift rotationPhase dipoleAngle offset).limitingDipoleAngle : ℂ))‖ ≤
        constant / time ^ 2 ∧
      ‖((separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time -
        (separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time) / 2 +
        Complex.I * Complex.exp (Complex.I * ((separatingCandidate timeShift rotationPhase dipoleAngle offset).limitingDipoleAngle : ℂ)) *
          (time : ℂ) - (separatingCandidate timeShift rotationPhase dipoleAngle offset).limitingPairOffset‖ ≤ constant / time := by
  have exponentialProduct : Complex.exp (Complex.I * (rotationPhase : ℂ)) *
      Complex.exp (Complex.I * (dipoleAngle : ℂ)) =
      Complex.exp (Complex.I * ((rotationPhase + dipoleAngle : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  refine ⟨4 * bound, by positivity, 2 * |timeShift| + timeMin + 1, by positivity, ?_⟩
  intro time timeAbove
  have timePositive' : 0 < time := by linarith [abs_nonneg timeShift]
  have rawTimeAbove : timeMin ≤ time + timeShift := by linarith [neg_abs_le timeShift, abs_nonneg timeShift]
  have halfTime : time / 2 ≤ time + timeShift := by linarith [neg_abs_le timeShift]
  have rawTimePositive : 0 < time + timeShift := timePositive.trans_le rawTimeAbove
  have squareEstimate : bound / (time + timeShift) ^ 2 ≤ (4 * bound) / time ^ 2 := by
    calc
      _ ≤ bound / (time / 2) ^ 2 := div_le_div_of_nonneg_left boundPositive.le (by positivity) (by nlinarith)
      _ = _ := by field_simp; ring
  have linearEstimate : bound / (time + timeShift) ≤ (4 * bound) / time := by
    calc
      _ ≤ bound / (time / 2) := div_le_div_of_nonneg_left boundPositive.le (by positivity) halfTime
      _ = (2 * bound) / time := by field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) timePositive'.le
  have separationIdentity : (separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time +
      (separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time -
      Complex.exp (Complex.I * ((separatingCandidate timeShift rotationPhase dipoleAngle offset).limitingDipoleAngle : ℂ)) =
      Complex.exp (Complex.I * (rotationPhase : ℂ)) *
        (separatingPositive 1 (by norm_num) (time + timeShift) + separatingNegative 1 (by norm_num) (time + timeShift) -
          Complex.exp (Complex.I * (dipoleAngle : ℂ))) := by
    dsimp only [separatingCandidate]
    rw [← exponentialProduct]
    ring
  have centerIdentity : ((separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time -
      (separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time) / 2 +
      Complex.I * Complex.exp (Complex.I * ((separatingCandidate timeShift rotationPhase dipoleAngle offset).limitingDipoleAngle : ℂ)) *
        (time : ℂ) - (separatingCandidate timeShift rotationPhase dipoleAngle offset).limitingPairOffset =
      Complex.exp (Complex.I * (rotationPhase : ℂ)) *
        ((separatingPositive 1 (by norm_num) (time + timeShift) - separatingNegative 1 (by norm_num) (time + timeShift)) / 2 +
          Complex.I * Complex.exp (Complex.I * (dipoleAngle : ℂ)) * ((time + timeShift : ℝ) : ℂ) - offset) := by
    dsimp only [separatingCandidate]
    rw [← exponentialProduct]
    push_cast
    ring
  rw [separationIdentity, centerIdentity, norm_mul, norm_mul, separatingCandidate_rotation_norm, one_mul, one_mul]
  exact ⟨((rawError _ rawTimeAbove).1).trans squareEstimate, ((rawError _ rawTimeAbove).2).trans linearEstimate⟩

set_option maxHeartbeats 1200000 in
theorem normalizedSeparatingOrbit_exists : ∃ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit := by
  obtain ⟨coefficient, coefficientPositive, unstableLimit⟩ := separatingUnstableShape_incoming_exponential 1 (by norm_num)
  obtain ⟨phaseLimit, phaseLimitProperty⟩ := separatingPhase_incoming_limit 1 (by norm_num)
  obtain ⟨dipoleAngle, offset, bound, boundPositive, timeMin, timePositive, scattering⟩ :=
    separating_scattering_asymptotics 1 (by norm_num)
  simp only [Complex.ofReal_one, mul_one] at scattering
  simp only [mul_one] at unstableLimit phaseLimitProperty
  let timeShift : ℝ := -Real.log coefficient / (2 * Real.sqrt 2)
  let rotationPhase : ℝ := timeShift - phaseLimit
  have timeAtBot : Filter.Tendsto (fun time : ℝ => time + timeShift) Filter.atBot Filter.atBot :=
    Filter.tendsto_atBot_add_const_right _ _ tendsto_id
  have timeAtTop : Filter.Tendsto (fun time : ℝ => time + timeShift) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ tendsto_id
  have geometry := separatingCandidate_geometry timeShift rotationPhase dipoleAngle offset
  refine ⟨separatingCandidate timeShift rotationPhase dipoleAngle offset, ?_⟩
  unfold IsNormalizedSeparatingOrbit
  refine ⟨geometry.1, ?_, geometry.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro time
    have geometryTime := geometry.2.1 time
    have equations := separatingCandidate_pointEquations timeShift rotationPhase dipoleAngle time offset
    exact ⟨geometryTime.1, geometryTime.2, equations.1, equations.2⟩
  · have result := (separating_radial_incoming_limit 1 (by norm_num)).comp timeAtBot
    convert result using 1
    funext time
    have norms := separatingCandidate_norms timeShift rotationPhase dipoleAngle time offset
    rw [norms.1, norms.2]
    rfl
  · have result := (separating_angle_incoming_limit 1 (by norm_num)).comp timeAtBot
    apply result.congr'
    apply Filter.Eventually.of_forall
    intro time
    change 2 * Complex.arg (separatingNegative 1 (by norm_num) (time + timeShift) /
      separatingPositive 1 (by norm_num) (time + timeShift)) = 2 * Complex.arg
      ((separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time /
        (separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time)
    rw [separatingCandidate_ratio, separating_position_ratio]
  · have result := (unstableLimit.comp timeAtBot).const_mul (Real.exp ((2 * Real.sqrt 2) * timeShift))
    have exponent : (2 * Real.sqrt 2) * timeShift = -Real.log coefficient := by
      dsimp only [timeShift]
      field_simp
      <;> ring
    have normalizedConstant : Real.exp ((2 * Real.sqrt 2) * timeShift) * coefficient = 1 := by
      rw [exponent, Real.exp_neg, Real.exp_log coefficientPositive, inv_mul_cancel₀ coefficientPositive.ne']
    rw [normalizedConstant] at result
    apply result.congr'
    apply Filter.Eventually.of_forall
    intro time
    change Real.exp ((2 * Real.sqrt 2) * timeShift) *
      (Real.exp (-(2 * Real.sqrt 2) * (time + timeShift)) *
        separatingUnstableShape (separatingScalarOrbit 1 (by norm_num) (time + timeShift))) =
      Real.exp (-(2 * Real.sqrt 2) * time) *
        orbitUnstableShape (separatingCandidate timeShift rotationPhase dipoleAngle offset) time
    rw [(separatingCandidate_unstableStable timeShift rotationPhase dipoleAngle time offset).1]
    rw [← mul_assoc, ← Real.exp_add]
    congr 1
    congr 1
    ring
  · have result := (phaseLimitProperty.comp timeAtBot).add_const (rotationPhase - timeShift)
    convert result using 1
    · funext time
      dsimp only [separatingCandidate, Function.comp_def]
      ring
    · congr 1
      dsimp only [rotationPhase]
      ring
  · have result := (separatingStableShape_incoming_ratio 1 (by norm_num)).comp timeAtBot
    apply result.congr'
    apply Filter.Eventually.of_forall
    intro time
    change separatingStableShape (separatingScalarOrbit 1 (by norm_num) (time + timeShift)) /
      separatingUnstableShape (separatingScalarOrbit 1 (by norm_num) (time + timeShift)) =
      orbitStableShape (separatingCandidate timeShift rotationPhase dipoleAngle offset) time /
        orbitUnstableShape (separatingCandidate timeShift rotationPhase dipoleAngle offset) time
    rw [(separatingCandidate_unstableStable timeShift rotationPhase dipoleAngle time offset).1,
      (separatingCandidate_unstableStable timeShift rotationPhase dipoleAngle time offset).2]
  · have result := (separating_radial_outgoing_limit 1 (by norm_num)).comp timeAtTop
    convert result using 1
    funext time
    have norms := separatingCandidate_norms timeShift rotationPhase dipoleAngle time offset
    rw [norms.1, norms.2]
    rfl
  · have result := (separating_angle_outgoing_limit 1 (by norm_num)).comp timeAtTop
    apply result.congr'
    apply Filter.Eventually.of_forall
    intro time
    change 2 * Complex.arg (separatingNegative 1 (by norm_num) (time + timeShift) /
      separatingPositive 1 (by norm_num) (time + timeShift)) = 2 * Complex.arg
      ((separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time /
        (separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time)
    rw [separatingCandidate_ratio, separating_position_ratio]
  · exact separatingCandidate_scattering timeShift rotationPhase dipoleAngle offset boundPositive timePositive scattering

end EulerNonuniqueness.Paper
