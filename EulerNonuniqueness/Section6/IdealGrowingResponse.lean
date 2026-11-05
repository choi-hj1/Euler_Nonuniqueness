import EulerNonuniqueness.Section6.UnstableDuhamel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace EulerNonuniqueness.Section6

def idealGrowingResponse (frequency coefficient initial time : ℝ) : ℝ :=
  (initial + coefficient) * Real.exp (2 * Real.sqrt 2 * frequency * time) -
    coefficient * ((1 + 2 * Real.sqrt 2 * frequency * time) * Real.cos (2 * frequency * time) +
      2 * frequency * time * Real.sin (2 * frequency * time))

def idealGrowingInput (frequency coefficient time : ℝ) : ℝ :=
  4 * coefficient * frequency ^ 2 * time *
    (Real.cos (2 * frequency * time) + 2 * Real.sqrt 2 * Real.sin (2 * frequency * time))

theorem idealGrowingResponse_initial (frequency coefficient initial : ℝ) :
    idealGrowingResponse frequency coefficient initial 0 = initial := by
  simp [idealGrowingResponse]

theorem idealGrowingResponse_hasDerivAt (frequency coefficient initial time : ℝ) :
    HasDerivAt (idealGrowingResponse frequency coefficient initial)
      (2 * Real.sqrt 2 * frequency * idealGrowingResponse frequency coefficient initial time +
        idealGrowingInput frequency coefficient time) time := by
  have exponential := (((hasDerivAt_id time).const_mul (2 * Real.sqrt 2 * frequency)).exp).const_mul
    (initial + coefficient)
  have cosine := ((hasDerivAt_id time).const_mul (2 * frequency)).cos
  have sine := ((hasDerivAt_id time).const_mul (2 * frequency)).sin
  have linear := (hasDerivAt_id time).const_mul (2 * frequency)
  have growingLinear := (hasDerivAt_const time (1 : ℝ)).add
    ((hasDerivAt_id time).const_mul (2 * Real.sqrt 2 * frequency))
  convert exponential.sub (((growingLinear.mul cosine).add (linear.mul sine)).const_mul coefficient) using 1
  simp only [idealGrowingResponse, idealGrowingInput, id_eq, mul_one, zero_add]
  linear_combination (-4 * coefficient * frequency ^ 2 * time * Real.cos (2 * frequency * time)) *
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)

theorem idealGrowingInput_continuous (frequency coefficient : ℝ) :
    Continuous (idealGrowingInput frequency coefficient) := by
  unfold idealGrowingInput
  fun_prop

theorem idealGrowingInput_integral (frequency coefficient time : ℝ) (timeNonnegative : 0 ≤ time) :
    (∫ currentTime in (0 : ℝ)..time,
      Real.exp (-(2 * Real.sqrt 2 * frequency) * currentTime) *
        idealGrowingInput frequency coefficient currentTime) =
      coefficient - coefficient * Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
        ((1 + 2 * Real.sqrt 2 * frequency * time) * Real.cos (2 * frequency * time) +
          2 * frequency * time * Real.sin (2 * frequency * time)) := by
  have identity := scalar_duhamel (idealGrowingInput_continuous frequency coefficient).continuousOn
    (fun currentTime _ => idealGrowingResponse_hasDerivAt frequency coefficient 0 currentTime)
      timeNonnegative (le_refl time)
  rw [idealGrowingResponse_initial] at identity
  have cancellation : Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
      Real.exp (2 * Real.sqrt 2 * frequency * time) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have multiplied := congrArg (fun value => Real.exp (-(2 * Real.sqrt 2 * frequency) * time) * value) identity
  simp only [zero_add] at multiplied
  rw [← mul_assoc, cancellation, one_mul] at multiplied
  rw [← multiplied]
  unfold idealGrowingResponse
  simp only [zero_add, mul_sub, ← mul_assoc, cancellation, one_mul]
  linear_combination coefficient * cancellation

theorem maximizing_phase_trigonometry :
    Real.cos (Real.pi - Real.arctan (1 / Real.sqrt 2)) = -Real.sqrt 2 / Real.sqrt 3 ∧
    Real.sin (Real.pi - Real.arctan (1 / Real.sqrt 2)) = 1 / Real.sqrt 3 := by
  have sqrtTwoPositive : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have sqrtThreePositive : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have sqrtTwoSquare := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have sqrtThreeSquare := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have cosineSquare : Real.cos (Real.arctan (1 / Real.sqrt 2)) ^ 2 = 2 / 3 := by
    rw [Real.cos_sq_arctan]
    field_simp
    nlinarith
  have productSquare : (Real.sqrt 3 * Real.cos (Real.arctan (1 / Real.sqrt 2))) ^ 2 =
      (Real.sqrt 2) ^ 2 := by
    rw [mul_pow, sqrtThreeSquare, cosineSquare, sqrtTwoSquare]
    norm_num
  have cosineProduct : Real.sqrt 3 * Real.cos (Real.arctan (1 / Real.sqrt 2)) = Real.sqrt 2 := by
    nlinarith [mul_pos sqrtThreePositive (Real.cos_arctan_pos (1 / Real.sqrt 2))]
  have cosineValue : Real.cos (Real.arctan (1 / Real.sqrt 2)) = Real.sqrt 2 / Real.sqrt 3 := by
    exact (eq_div_iff sqrtThreePositive.ne').mpr (by nlinarith)
  have tangentIdentity := Real.tan_arctan (1 / Real.sqrt 2)
  rw [Real.tan_eq_sin_div_cos, cosineValue] at tangentIdentity
  have sineValue : Real.sin (Real.arctan (1 / Real.sqrt 2)) = 1 / Real.sqrt 3 := by
    field_simp at tangentIdentity ⊢
    nlinarith
  rw [Real.cos_sub, Real.sin_sub, Real.cos_pi, Real.sin_pi]
  simp only [neg_mul, one_mul, zero_mul, zero_sub, sub_zero]
  constructor
  · rw [cosineValue]; ring
  · simpa using sineValue

theorem ideal_strain_maximizing_input (frequency strainAmplitude time : ℝ)
    (frequencyNonzero : frequency ≠ 0) :
    -2 * (strainAmplitude * time * Real.cos
      (Real.pi - Real.arctan (1 / Real.sqrt 2) + 2 * frequency * time)) -
      Real.sqrt 2 * (strainAmplitude * time * Real.sin
        (Real.pi - Real.arctan (1 / Real.sqrt 2) + 2 * frequency * time)) =
      idealGrowingInput frequency
        (strainAmplitude * Real.sqrt 2 / (4 * Real.sqrt 3 * frequency ^ 2)) time := by
  rw [Real.cos_add, Real.sin_add, maximizing_phase_trigonometry.1,
    maximizing_phase_trigonometry.2]
  unfold idealGrowingInput
  have sqrtThreeNonzero : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)).ne'
  field_simp [frequencyNonzero, sqrtThreeNonzero]
  have cube : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    calc
      _ = Real.sqrt 3 ^ 2 * Real.sqrt 3 := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring_nf
  rw [cube, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem vanishing_weight_mul_cos {weight phase : ℝ → ℝ}
    (weightLimit : Filter.Tendsto weight Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun time => weight time * Real.cos (phase time)) Filter.atTop (nhds 0) := by
  have bound : ∀ time, ‖weight time * Real.cos (phase time)‖ ≤ |weight time| := by
    intro time
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  exact squeeze_zero_norm bound (by simpa only [Real.norm_eq_abs, norm_zero] using weightLimit.norm)

theorem vanishing_weight_mul_sin {weight phase : ℝ → ℝ}
    (weightLimit : Filter.Tendsto weight Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun time => weight time * Real.sin (phase time)) Filter.atTop (nhds 0) := by
  have bound : ∀ time, ‖weight time * Real.sin (phase time)‖ ≤ |weight time| := by
    intro time
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  exact squeeze_zero_norm bound (by simpa only [Real.norm_eq_abs, norm_zero] using weightLimit.norm)

theorem exponential_linear_decay {rate : ℝ} (ratePositive : 0 < rate) :
    Filter.Tendsto (fun time : ℝ => time * Real.exp (-rate * time)) Filter.atTop (nhds 0) := by
  have scaled := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (Filter.tendsto_id.const_mul_atTop ratePositive)
  have divided := scaled.div_const rate
  convert divided using 1
  · funext time
    simp only [Function.comp_apply, pow_one]
    field_simp
    ring
  · simp

theorem idealGrowingInput_weighted_integral_limit (frequency coefficient : ℝ)
    (frequencyPositive : 0 < frequency) :
    Filter.Tendsto (fun time => ∫ currentTime in (0 : ℝ)..time,
      Real.exp (-(2 * Real.sqrt 2 * frequency) * currentTime) *
        idealGrowingInput frequency coefficient currentTime) Filter.atTop (nhds coefficient) := by
  have ratePositive : 0 < 2 * Real.sqrt 2 * frequency := by positivity
  have expLimit : Filter.Tendsto (fun time : ℝ => Real.exp (-(2 * Real.sqrt 2 * frequency) * time))
      Filter.atTop (nhds 0) := by
    simpa only [neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.tendsto_id.const_mul_atTop ratePositive)
  have linearLimit := exponential_linear_decay ratePositive
  have cosineWeight : Filter.Tendsto (fun time : ℝ =>
      Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
        (1 + 2 * Real.sqrt 2 * frequency * time)) Filter.atTop (nhds 0) := by
    convert expLimit.add (linearLimit.const_mul (2 * Real.sqrt 2 * frequency)) using 1
    · funext time; ring
    · simp
  have sineWeight : Filter.Tendsto (fun time : ℝ =>
      Real.exp (-(2 * Real.sqrt 2 * frequency) * time) * (2 * frequency * time))
        Filter.atTop (nhds 0) := by
    convert linearLimit.const_mul (2 * frequency) using 1
    · funext time; ring
    · simp
  have tailLimit := ((vanishing_weight_mul_cos (phase := fun time => 2 * frequency * time) cosineWeight).add
    (vanishing_weight_mul_sin (phase := fun time => 2 * frequency * time) sineWeight)).const_mul coefficient
  have result := (tendsto_const_nhds (x := coefficient)).sub tailLimit
  simp only [add_zero, mul_zero, sub_zero] at result
  apply result.congr'
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with time timeNonnegative
  rw [idealGrowingInput_integral frequency coefficient time timeNonnegative]
  ring

theorem idealGrowingInput_weighted_integrable (frequency coefficient : ℝ)
    (frequencyPositive : 0 < frequency) :
    IntegrableOn (fun time => Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
      idealGrowingInput frequency coefficient time) (Ioi 0) := by
  have ratePositive : 0 < 2 * Real.sqrt 2 * frequency := by positivity
  have baseIntegrable : IntegrableOn (fun time : ℝ => time *
      Real.exp (-(2 * Real.sqrt 2 * frequency) * time)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 1) (b := 2 * Real.sqrt 2 * frequency)
      (by norm_num) (by norm_num) ratePositive
  have envelopeIntegrable := baseIntegrable.const_mul
    (4 * |coefficient| * frequency ^ 2 * (1 + 2 * Real.sqrt 2))
  apply envelopeIntegrable.mono'
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (idealGrowingInput_continuous frequency coefficient)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with time timePositive
    have timePositive' : 0 < time := timePositive
    have trigBound : |Real.cos (2 * frequency * time) + 2 * Real.sqrt 2 * Real.sin (2 * frequency * time)| ≤
        1 + 2 * Real.sqrt 2 := by
      calc
        _ ≤ |Real.cos (2 * frequency * time)| + |2 * Real.sqrt 2 * Real.sin (2 * frequency * time)| := abs_add _ _
        _ ≤ _ := by
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt 2)]
          exact add_le_add (Real.abs_cos_le_one _) (by
            simpa using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (2 * frequency * time))
              (by positivity : 0 ≤ 2 * Real.sqrt 2))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have inputBound : |idealGrowingInput frequency coefficient time| ≤
        4 * |coefficient| * frequency ^ 2 * time * (1 + 2 * Real.sqrt 2) := by
      unfold idealGrowingInput
      rw [abs_mul]
      simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num), abs_pow,
        abs_of_pos timePositive']
      simpa only [sq_abs] using mul_le_mul_of_nonneg_left trigBound
        (show 0 ≤ 4 * |coefficient| * frequency ^ 2 * time by positivity)
    calc
      _ ≤ Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
          (4 * |coefficient| * frequency ^ 2 * time * (1 + 2 * Real.sqrt 2)) :=
        mul_le_mul_of_nonneg_left inputBound (Real.exp_pos _).le
      _ = _ := by ring

theorem idealGrowingInput_weighted_integral (frequency coefficient : ℝ)
    (frequencyPositive : 0 < frequency) :
    (∫ time : ℝ in Ioi 0, Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
      idealGrowingInput frequency coefficient time) = coefficient := by
  exact tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi 0
      (idealGrowingInput_weighted_integrable frequency coefficient frequencyPositive) Filter.tendsto_id)
    (idealGrowingInput_weighted_integral_limit frequency coefficient frequencyPositive)

theorem ideal_strain_positive_coefficient (frequency strainAmplitude : ℝ)
    (frequencyPositive : 0 < frequency) (amplitudePositive : 0 < strainAmplitude) :
    (∫ time : ℝ in Ioi 0, Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
      (-2 * (strainAmplitude * time * Real.cos
        (Real.pi - Real.arctan (1 / Real.sqrt 2) + 2 * frequency * time)) -
        Real.sqrt 2 * (strainAmplitude * time * Real.sin
          (Real.pi - Real.arctan (1 / Real.sqrt 2) + 2 * frequency * time)))) =
        strainAmplitude * Real.sqrt 2 / (4 * Real.sqrt 3 * frequency ^ 2) ∧
    0 < strainAmplitude * Real.sqrt 2 / (4 * Real.sqrt 3 * frequency ^ 2) := by
  constructor
  · simp_rw [ideal_strain_maximizing_input frequency strainAmplitude _ frequencyPositive.ne']
    exact idealGrowingInput_weighted_integral _ _ frequencyPositive
  · positivity

theorem sqrt_two_cos_add_sin_bound (phase : ℝ) :
    |Real.sqrt 2 * Real.cos phase + Real.sin phase| ≤ Real.sqrt 3 := by
  have identity : (Real.sqrt 2 * Real.cos phase + Real.sin phase) ^ 2 +
      (Real.cos phase - Real.sqrt 2 * Real.sin phase) ^ 2 = 3 := by
    linear_combination (Real.cos phase ^ 2 + Real.sin phase ^ 2) *
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num) +
        3 * Real.sin_sq_add_cos_sq phase
  nlinarith [sq_nonneg (Real.cos phase - Real.sqrt 2 * Real.sin phase),
    sq_abs (Real.sqrt 2 * Real.cos phase + Real.sin phase),
    Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]

theorem idealGrowingResponse_error (frequency coefficient initial time : ℝ)
    (frequencyNonnegative : 0 ≤ frequency) (coefficientNonnegative : 0 ≤ coefficient)
    (timeNonnegative : 0 ≤ time) :
    |idealGrowingResponse frequency coefficient initial time -
      (initial + coefficient) * Real.exp (2 * Real.sqrt 2 * frequency * time)| ≤
        coefficient * (1 + 2 * Real.sqrt 3 * frequency * time) := by
  have trigBound := sqrt_two_cos_add_sin_bound (2 * frequency * time)
  have bracketBound : |(1 + 2 * Real.sqrt 2 * frequency * time) * Real.cos (2 * frequency * time) +
      2 * frequency * time * Real.sin (2 * frequency * time)| ≤
        1 + 2 * Real.sqrt 3 * frequency * time := by
    calc
      _ = |Real.cos (2 * frequency * time) + 2 * frequency * time *
          (Real.sqrt 2 * Real.cos (2 * frequency * time) + Real.sin (2 * frequency * time))| := by congr 1; ring
      _ ≤ |Real.cos (2 * frequency * time)| + |2 * frequency * time *
          (Real.sqrt 2 * Real.cos (2 * frequency * time) + Real.sin (2 * frequency * time))| := abs_add _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * frequency * time)]
        have bound := mul_le_mul_of_nonneg_left trigBound
          (show 0 ≤ 2 * frequency * time by positivity)
        nlinarith [Real.abs_cos_le_one (2 * frequency * time)]
  have differenceIdentity : idealGrowingResponse frequency coefficient initial time -
      (initial + coefficient) * Real.exp (2 * Real.sqrt 2 * frequency * time) =
      -coefficient * ((1 + 2 * Real.sqrt 2 * frequency * time) * Real.cos (2 * frequency * time) +
        2 * frequency * time * Real.sin (2 * frequency * time)) := by
    unfold idealGrowingResponse
    ring
  rw [differenceIdentity, abs_mul, abs_neg, abs_of_nonneg coefficientNonnegative]
  exact mul_le_mul_of_nonneg_left bracketBound coefficientNonnegative

def idealQuadratureResponse (frequency coefficient time : ℝ) : ℝ :=
  coefficient * ((1 + 2 * Real.sqrt 2 * frequency * time) * Real.sin (2 * frequency * time) -
    2 * frequency * time * Real.cos (2 * frequency * time))

def idealQuadratureInput (frequency coefficient time : ℝ) : ℝ :=
  4 * coefficient * frequency ^ 2 * time *
    (2 * Real.sqrt 2 * Real.cos (2 * frequency * time) - Real.sin (2 * frequency * time))

theorem idealQuadratureResponse_hasDerivAt (frequency coefficient time : ℝ) :
    HasDerivAt (idealQuadratureResponse frequency coefficient)
      (2 * Real.sqrt 2 * frequency * idealQuadratureResponse frequency coefficient time +
        idealQuadratureInput frequency coefficient time) time := by
  have cosine := ((hasDerivAt_id time).const_mul (2 * frequency)).cos
  have sine := ((hasDerivAt_id time).const_mul (2 * frequency)).sin
  have linear := (hasDerivAt_id time).const_mul (2 * frequency)
  have growingLinear := (hasDerivAt_const time (1 : ℝ)).add
    ((hasDerivAt_id time).const_mul (2 * Real.sqrt 2 * frequency))
  convert ((growingLinear.mul sine).sub (linear.mul cosine)).const_mul coefficient using 1
  simp only [idealQuadratureResponse, idealQuadratureInput, id_eq, mul_one, zero_add]
  linear_combination (4 * coefficient * frequency ^ 2 * time * Real.sin (2 * frequency * time)) *
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)

theorem idealQuadratureInput_integral (frequency coefficient time : ℝ) (timeNonnegative : 0 ≤ time) :
    (∫ currentTime in (0 : ℝ)..time,
      Real.exp (-(2 * Real.sqrt 2 * frequency) * currentTime) *
        idealQuadratureInput frequency coefficient currentTime) =
      Real.exp (-(2 * Real.sqrt 2 * frequency) * time) * idealQuadratureResponse frequency coefficient time := by
  have inputContinuous : Continuous (idealQuadratureInput frequency coefficient) := by
    unfold idealQuadratureInput
    fun_prop
  have identity := scalar_duhamel inputContinuous.continuousOn
    (fun currentTime _ => idealQuadratureResponse_hasDerivAt frequency coefficient currentTime)
      timeNonnegative (le_refl time)
  have initialIdentity : idealQuadratureResponse frequency coefficient 0 = 0 := by
    simp [idealQuadratureResponse]
  rw [initialIdentity, zero_add] at identity
  have cancellation : Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
      Real.exp (2 * Real.sqrt 2 * frequency * time) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [identity, ← mul_assoc, cancellation, one_mul]

theorem weighted_linear_integrable {input : ℝ → ℝ} {rate bound : ℝ}
    (ratePositive : 0 < rate) (inputContinuous : Continuous input)
    (inputBound : ∀ time : ℝ, 0 < time → |input time| ≤ bound * time) :
    IntegrableOn (fun time => Real.exp (-rate * time) * input time) (Ioi 0) := by
  have baseIntegrable : IntegrableOn (fun time : ℝ => time * Real.exp (-rate * time)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 1) (b := rate) (by norm_num) (by norm_num) ratePositive
  apply (baseIntegrable.const_mul bound).mono'
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      inputContinuous).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with time timePositive
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-rate * time) * (bound * time) :=
        mul_le_mul_of_nonneg_left (inputBound time timePositive) (Real.exp_pos _).le
      _ = _ := by ring

theorem exponential_affine_decay {rate : ℝ} (ratePositive : 0 < rate) (constant slope : ℝ) :
    Filter.Tendsto (fun time : ℝ => Real.exp (-rate * time) * (constant + slope * time))
      Filter.atTop (nhds 0) := by
  have expLimit : Filter.Tendsto (fun time : ℝ => Real.exp (-rate * time)) Filter.atTop (nhds 0) := by
    simpa only [neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.tendsto_id.const_mul_atTop ratePositive)
  convert (expLimit.const_mul constant).add ((exponential_linear_decay ratePositive).const_mul slope) using 1
  · funext time; ring
  · simp

theorem idealQuadratureInput_weighted_integral_limit (frequency coefficient : ℝ)
    (frequencyPositive : 0 < frequency) :
    Filter.Tendsto (fun time => ∫ currentTime in (0 : ℝ)..time,
      Real.exp (-(2 * Real.sqrt 2 * frequency) * currentTime) *
        idealQuadratureInput frequency coefficient currentTime) Filter.atTop (nhds 0) := by
  have ratePositive : 0 < 2 * Real.sqrt 2 * frequency := by positivity
  have sineLimit := vanishing_weight_mul_sin (phase := fun time => 2 * frequency * time)
    (exponential_affine_decay ratePositive 1 (2 * Real.sqrt 2 * frequency))
  have cosineLimit := vanishing_weight_mul_cos (phase := fun time => 2 * frequency * time)
    (exponential_affine_decay ratePositive 0 (2 * frequency))
  have result := (sineLimit.sub cosineLimit).const_mul coefficient
  simp only [sub_zero, mul_zero] at result
  apply result.congr'
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with time timeNonnegative
  rw [idealQuadratureInput_integral frequency coefficient time timeNonnegative]
  unfold idealQuadratureResponse
  ring

theorem idealQuadratureInput_weighted_integrable (frequency coefficient : ℝ)
    (frequencyPositive : 0 < frequency) :
    IntegrableOn (fun time => Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
      idealQuadratureInput frequency coefficient time) (Ioi 0) := by
  have ratePositive : 0 < 2 * Real.sqrt 2 * frequency := by positivity
  have inputContinuous : Continuous (idealQuadratureInput frequency coefficient) := by
    unfold idealQuadratureInput
    fun_prop
  apply weighted_linear_integrable ratePositive inputContinuous
    (bound := 4 * |coefficient| * frequency ^ 2 * (2 * Real.sqrt 2 + 1))
  intro time timePositive
  have trigBound : |2 * Real.sqrt 2 * Real.cos (2 * frequency * time) - Real.sin (2 * frequency * time)| ≤
      2 * Real.sqrt 2 + 1 := by
    calc
      _ ≤ |2 * Real.sqrt 2 * Real.cos (2 * frequency * time)| + |Real.sin (2 * frequency * time)| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt 2)]
        exact add_le_add (by
          simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (2 * frequency * time))
            (by positivity : 0 ≤ 2 * Real.sqrt 2)) (Real.abs_sin_le_one _)
  unfold idealQuadratureInput
  rw [abs_mul]
  simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num), abs_pow,
    abs_of_pos timePositive, sq_abs]
  have bound := mul_le_mul_of_nonneg_left trigBound
    (show 0 ≤ 4 * |coefficient| * frequency ^ 2 * time by positivity)
  nlinarith

theorem idealQuadratureInput_weighted_integral (frequency coefficient : ℝ)
    (frequencyPositive : 0 < frequency) :
    (∫ time : ℝ in Ioi 0, Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
      idealQuadratureInput frequency coefficient time) = 0 := by
  exact tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi 0
      (idealQuadratureInput_weighted_integrable frequency coefficient frequencyPositive) Filter.tendsto_id)
    (idealQuadratureInput_weighted_integral_limit frequency coefficient frequencyPositive)

def idealStrainInput (frequency strainAmplitude phase time : ℝ) : ℝ :=
  -2 * (strainAmplitude * time * Real.cos (phase + 2 * frequency * time)) -
    Real.sqrt 2 * (strainAmplitude * time * Real.sin (phase + 2 * frequency * time))

theorem idealStrainInput_phase_decomposition (frequency strainAmplitude offset time : ℝ)
    (frequencyNonzero : frequency ≠ 0) :
    idealStrainInput frequency strainAmplitude
      (Real.pi - Real.arctan (1 / Real.sqrt 2) + offset) time =
    Real.cos offset * idealGrowingInput frequency
      (strainAmplitude * Real.sqrt 2 / (4 * Real.sqrt 3 * frequency ^ 2)) time +
    Real.sin offset * idealQuadratureInput frequency
      (strainAmplitude * Real.sqrt 2 / (4 * Real.sqrt 3 * frequency ^ 2)) time := by
  unfold idealStrainInput idealGrowingInput idealQuadratureInput
  simp only [Real.cos_add, Real.sin_add, maximizing_phase_trigonometry.1,
    maximizing_phase_trigonometry.2]
  have sqrtThreeNonzero : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)).ne'
  field_simp [frequencyNonzero, sqrtThreeNonzero]
  have fourthPower : Real.sqrt 3 ^ 4 = 9 := by
    calc
      _ = (Real.sqrt 3 ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
  ring_nf
  rw [fourthPower, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

theorem idealStrainInput_weighted_integral (frequency strainAmplitude offset : ℝ)
    (frequencyPositive : 0 < frequency) :
    (∫ time : ℝ in Ioi 0, Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
      idealStrainInput frequency strainAmplitude
        (Real.pi - Real.arctan (1 / Real.sqrt 2) + offset) time) =
      (strainAmplitude * Real.sqrt 2 / (4 * Real.sqrt 3 * frequency ^ 2)) * Real.cos offset := by
  have integrandIdentity : (fun time => Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
      idealStrainInput frequency strainAmplitude
        (Real.pi - Real.arctan (1 / Real.sqrt 2) + offset) time) =
      (fun time => Real.cos offset * (Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
        idealGrowingInput frequency (strainAmplitude * Real.sqrt 2 / (4 * Real.sqrt 3 * frequency ^ 2)) time) +
        Real.sin offset * (Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
          idealQuadratureInput frequency (strainAmplitude * Real.sqrt 2 / (4 * Real.sqrt 3 * frequency ^ 2)) time)) := by
    funext time
    rw [idealStrainInput_phase_decomposition _ _ _ _ frequencyPositive.ne']
    ring
  rw [integrandIdentity, integral_add
    ((idealGrowingInput_weighted_integrable _ _ frequencyPositive).const_mul (Real.cos offset))
    ((idealQuadratureInput_weighted_integrable _ _ frequencyPositive).const_mul (Real.sin offset)),
    integral_const_mul, integral_const_mul, idealGrowingInput_weighted_integral _ _ frequencyPositive,
    idealQuadratureInput_weighted_integral _ _ frequencyPositive]
  ring

theorem ideal_strain_source_coefficient (frequency circulation distance phase : ℝ)
    (frequencyPositive : 0 < frequency) (distancePositive : 0 < distance) :
    (∫ time : ℝ in Ioi 0, Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
      idealStrainInput frequency (3 * circulation ^ 2 / (Real.pi ^ 2 * distance ^ 4)) phase time) =
      Real.sqrt 3 * circulation ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * frequency ^ 2 * distance ^ 4) *
        Real.cos (phase + Real.arctan (1 / Real.sqrt 2) - Real.pi) := by
  have inputPhase : Real.pi - Real.arctan (1 / Real.sqrt 2) +
      (phase + Real.arctan (1 / Real.sqrt 2) - Real.pi) = phase := by ring
  have coefficientIdentity :
      (3 * circulation ^ 2 / (Real.pi ^ 2 * distance ^ 4)) * Real.sqrt 2 /
        (4 * Real.sqrt 3 * frequency ^ 2) =
      Real.sqrt 3 * circulation ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * frequency ^ 2 * distance ^ 4) := by
    have sqrtTwoNonzero : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
    have sqrtThreeNonzero : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)).ne'
    field_simp [frequencyPositive.ne', distancePositive.ne', Real.pi_ne_zero, sqrtTwoNonzero, sqrtThreeNonzero]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  have result := idealStrainInput_weighted_integral frequency
    (3 * circulation ^ 2 / (Real.pi ^ 2 * distance ^ 4))
    (phase + Real.arctan (1 / Real.sqrt 2) - Real.pi) frequencyPositive
  rw [inputPhase, coefficientIdentity] at result
  exact result

theorem ideal_strain_phase_robustness (frequency strainAmplitude offset : ℝ)
    (frequencyPositive : 0 < frequency) (amplitudeNonnegative : 0 ≤ strainAmplitude) :
    let coefficient := strainAmplitude * Real.sqrt 2 / (4 * Real.sqrt 3 * frequency ^ 2)
    let actual := ∫ time : ℝ in Ioi 0, Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
      idealStrainInput frequency strainAmplitude
        (Real.pi - Real.arctan (1 / Real.sqrt 2) + offset) time
    actual ≤ coefficient ∧ |actual - coefficient| ≤ coefficient * offset ^ 2 / 2 := by
  dsimp only
  rw [idealStrainInput_weighted_integral _ _ _ frequencyPositive]
  have coefficientNonnegative : 0 ≤ strainAmplitude * Real.sqrt 2 / (4 * Real.sqrt 3 * frequency ^ 2) := by
    positivity
  have upperBound := mul_le_mul_of_nonneg_left (Real.cos_le_one offset) coefficientNonnegative
  simp only [mul_one] at upperBound
  refine ⟨upperBound, ?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr upperBound)]
  have quadraticBound := mul_le_mul_of_nonneg_left
    (Real.one_sub_sq_div_two_le_cos (x := offset)) coefficientNonnegative
  nlinarith

end EulerNonuniqueness.Section6
