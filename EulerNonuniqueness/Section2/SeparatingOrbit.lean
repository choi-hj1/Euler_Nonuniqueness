import EulerNonuniqueness.Section2.RotatingRhombus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

namespace EulerNonuniqueness.Section2

def separatingScalarVelocity (frequency rootRatio : ℝ) : ℝ :=
  frequency / 4 * Real.sqrt (1 - rootRatio ^ 2) ^ 3 / rootRatio ^ 2 *
    (rootRatio ^ 2 + 2 * rootRatio - 1) *
    Real.sqrt (rootRatio ^ 2 + 4 * rootRatio - 1)

def separatingScalarLinearFactor (frequency rootRatio : ℝ) : ℝ :=
  frequency / 4 * Real.sqrt (1 - rootRatio ^ 2) ^ 3 / rootRatio ^ 2 *
    (rootRatio + Real.sqrt 2 + 1) *
    Real.sqrt (rootRatio ^ 2 + 4 * rootRatio - 1)

theorem separatingScalarVelocity_factorization (frequency rootRatio : ℝ) :
    separatingScalarVelocity frequency rootRatio =
      (rootRatio - (Real.sqrt 2 - 1)) *
        separatingScalarLinearFactor frequency rootRatio := by
  have factorization : rootRatio ^ 2 + 2 * rootRatio - 1 =
      (rootRatio - (Real.sqrt 2 - 1)) * (rootRatio + Real.sqrt 2 + 1) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  unfold separatingScalarVelocity separatingScalarLinearFactor
  rw [factorization]
  ring

theorem separatingScalarVelocity_pos (frequency rootRatio : ℝ)
    (frequencyPositive : 0 < frequency)
    (aboveRhombus : Real.sqrt 2 - 1 < rootRatio) (belowOne : rootRatio < 1) :
    0 < separatingScalarVelocity frequency rootRatio := by
  have rootPositive : 0 < rootRatio := by linarith [sqrt_two_gt_one]
  have firstPositive : 0 < rootRatio ^ 2 + 2 * rootRatio - 1 := by
    have := mul_pos (sub_pos.mpr aboveRhombus)
      (show 0 < rootRatio + Real.sqrt 2 + 1 by linarith [sqrt_two_gt_one])
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have secondPositive : 0 < rootRatio ^ 2 + 4 * rootRatio - 1 := by
    nlinarith
  have endpointPositive : 0 < 1 - rootRatio ^ 2 := by nlinarith
  unfold separatingScalarVelocity
  positivity

theorem separatingScalarVelocity_eq_rpow {frequency rootRatio : ℝ}
    (rootNonnegative : 0 ≤ rootRatio) (belowOne : rootRatio ≤ 1) :
    separatingScalarVelocity frequency rootRatio =
      frequency / 4 * (1 - rootRatio ^ 2) ^ (3 / 2 : ℝ) / rootRatio ^ 2 *
        (rootRatio ^ 2 + 2 * rootRatio - 1) *
        Real.sqrt (rootRatio ^ 2 + 4 * rootRatio - 1) := by
  have endpointNonnegative : 0 ≤ 1 - rootRatio ^ 2 := by nlinarith
  unfold separatingScalarVelocity
  rw [Real.rpow_div_two_eq_sqrt 3 endpointNonnegative]
  exact congrArg (fun value : ℝ => frequency / 4 * value / rootRatio ^ 2 *
    (rootRatio ^ 2 + 2 * rootRatio - 1) * Real.sqrt (rootRatio ^ 2 + 4 * rootRatio - 1))
    (Real.rpow_natCast (Real.sqrt (1 - rootRatio ^ 2)) 3).symm

theorem separatingScalarLinearFactor_at_rhombus (frequency : ℝ) :
    separatingScalarLinearFactor frequency (Real.sqrt 2 - 1) =
      2 * Real.sqrt 2 * frequency := by
  have square := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have rootPositive : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_gt_one]
  have first : 1 - (Real.sqrt 2 - 1) ^ 2 = 2 * (Real.sqrt 2 - 1) := by nlinarith
  have second : (Real.sqrt 2 - 1) ^ 2 + 4 * (Real.sqrt 2 - 1) - 1 =
      2 * (Real.sqrt 2 - 1) := by nlinarith
  have radicalSquare := Real.sq_sqrt (show 0 ≤ 2 * (Real.sqrt 2 - 1) by positivity)
  unfold separatingScalarLinearFactor
  rw [first, second]
  have radicalFourth : Real.sqrt (2 * (Real.sqrt 2 - 1)) ^ 3 *
      Real.sqrt (2 * (Real.sqrt 2 - 1)) = 4 * (Real.sqrt 2 - 1) ^ 2 := by
    calc
      _ = (Real.sqrt (2 * (Real.sqrt 2 - 1)) ^ 2) ^ 2 := by ring
      _ = _ := by rw [radicalSquare]; ring
  calc
    _ = frequency / 4 / (Real.sqrt 2 - 1) ^ 2 *
        (Real.sqrt (2 * (Real.sqrt 2 - 1)) ^ 3 *
          Real.sqrt (2 * (Real.sqrt 2 - 1))) *
        (Real.sqrt 2 - 1 + Real.sqrt 2 + 1) := by ring
    _ = _ := by rw [radicalFourth]; field_simp; ring

theorem separatingScalarLinearFactor_continuousAt_rhombus (frequency : ℝ) :
    ContinuousAt (separatingScalarLinearFactor frequency) (Real.sqrt 2 - 1) := by
  have rootNonzero : Real.sqrt 2 - 1 ≠ 0 := by linarith [sqrt_two_gt_one]
  unfold separatingScalarLinearFactor
  fun_prop (disch := positivity)

theorem separatingScalarVelocity_hasDerivAt_rhombus (frequency : ℝ) :
    HasDerivAt (separatingScalarVelocity frequency)
      (2 * Real.sqrt 2 * frequency) (Real.sqrt 2 - 1) := by
  have factorDerivative : HasDerivAt (fun rootRatio : ℝ => rootRatio - (Real.sqrt 2 - 1))
      1 (Real.sqrt 2 - 1) := (hasDerivAt_id _).sub_const _
  have rootNonzero : Real.sqrt 2 - 1 ≠ 0 := by linarith [sqrt_two_gt_one]
  have firstNonzero : 1 - (Real.sqrt 2 - 1) ^ 2 ≠ 0 := by
    nlinarith [sqrt_two_gt_one, sqrt_two_lt_three_halves,
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have secondNonzero : (Real.sqrt 2 - 1) ^ 2 + 4 * (Real.sqrt 2 - 1) - 1 ≠ 0 := by
    nlinarith [sqrt_two_gt_one, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have factorDifferentiable : DifferentiableAt ℝ (separatingScalarLinearFactor frequency)
      (Real.sqrt 2 - 1) := by
    have firstDerivative := ((hasDerivAt_const (Real.sqrt 2 - 1) (1 : ℝ)).sub
      ((hasDerivAt_id _).pow 2)).sqrt firstNonzero
    have secondDerivative := ((((hasDerivAt_id (Real.sqrt 2 - 1)).pow 2).add
      ((hasDerivAt_id _).const_mul 4)).sub_const 1).sqrt secondNonzero
    unfold separatingScalarLinearFactor
    exact (((differentiableAt_const _).mul (firstDerivative.differentiableAt.pow 3)).div
      (differentiableAt_id.pow 2) (pow_ne_zero 2 rootNonzero)).mul
      (((differentiableAt_id.add_const _).add_const _)) |>.mul
      secondDerivative.differentiableAt
  convert factorDerivative.mul factorDifferentiable.hasDerivAt using 1
  · funext rootRatio
    exact separatingScalarVelocity_factorization frequency rootRatio
  · simp [separatingScalarLinearFactor_at_rhombus]

def separatingEscapeVelocity (frequency rootRatio : ℝ) : ℝ :=
  frequency / 4 * (rootRatio ^ 2 + 2 * rootRatio - 1) *
    Real.sqrt (rootRatio ^ 2 + 4 * rootRatio - 1) / rootRatio

theorem separatingEscapeVelocity_at_one (frequency : ℝ) :
    separatingEscapeVelocity frequency 1 = frequency := by
  norm_num [separatingEscapeVelocity]
  ring

theorem separatingEscapeVelocity_continuousAt_one (frequency : ℝ) :
    ContinuousAt (separatingEscapeVelocity frequency) 1 := by
  unfold separatingEscapeVelocity
  fun_prop (disch := norm_num)

theorem separating_escape_coordinate_derivative
    {frequency : ℝ} {rootRatio : ℝ → ℝ} {time : ℝ}
    (rootPositive : 0 < rootRatio time) (belowOne : rootRatio time < 1)
    (trajectoryDerivative : HasDerivAt rootRatio
      (separatingScalarVelocity frequency (rootRatio time)) time) :
    HasDerivAt (fun currentTime => (Real.sqrt (1 - rootRatio currentTime ^ 2))⁻¹)
      (separatingEscapeVelocity frequency (rootRatio time)) time := by
  have endpointPositive : 0 < 1 - rootRatio time ^ 2 := by nlinarith
  have radicalPositive : 0 < Real.sqrt (1 - rootRatio time ^ 2) :=
    Real.sqrt_pos.mpr endpointPositive
  have radicalSquare := Real.sq_sqrt endpointPositive.le
  have result := (((hasDerivAt_const time (1 : ℝ)).sub
    (trajectoryDerivative.pow 2)).sqrt endpointPositive.ne').inv radicalPositive.ne'
  convert result using 1
  unfold separatingEscapeVelocity separatingScalarVelocity
  field_simp only [rootPositive.ne', radicalPositive.ne', pow_ne_zero, ne_of_gt
    (show (0 : ℝ) < 2 by norm_num), ne_of_gt (show (0 : ℝ) < 4 by norm_num)]
  ring

theorem separating_escape_coordinate_velocity_limit
    {frequency : ℝ} {rootRatio : ℝ → ℝ}
    (outgoingLimit : Filter.Tendsto rootRatio Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun time => separatingEscapeVelocity frequency (rootRatio time))
      Filter.atTop (nhds frequency) := by
  convert (separatingEscapeVelocity_continuousAt_one frequency).tendsto.comp
    outgoingLimit using 1
  rw [separatingEscapeVelocity_at_one]

theorem separating_quadrature_hasDerivAt
    (frequency rootRatio : ℝ) (frequencyPositive : 0 < frequency)
    (aboveRhombus : Real.sqrt 2 - 1 < rootRatio) (belowOne : rootRatio < 1) :
    HasDerivAt
      (fun endpoint => ∫ value in rootRatio..endpoint,
        (separatingScalarVelocity frequency value)⁻¹)
      (separatingScalarVelocity frequency rootRatio)⁻¹ rootRatio := by
  have rootPositive : 0 < rootRatio := by linarith [sqrt_two_gt_one]
  have velocityPositive := separatingScalarVelocity_pos frequency rootRatio
    frequencyPositive aboveRhombus belowOne
  have velocityContinuous : ContinuousAt (separatingScalarVelocity frequency) rootRatio := by
    unfold separatingScalarVelocity
    fun_prop (disch := positivity)
  have measurable : Measurable (fun value => (separatingScalarVelocity frequency value)⁻¹) := by
    unfold separatingScalarVelocity
    fun_prop
  exact intervalIntegral.integral_hasDerivAt_right
    (IntervalIntegrable.refl) measurable.stronglyMeasurable.stronglyMeasurableAtFilter
    (velocityContinuous.inv₀ velocityPositive.ne')

def separatingQuadrature (frequency rootRatio : ℝ) : ℝ :=
  ∫ value in (1 / 2 : ℝ)..rootRatio, (separatingScalarVelocity frequency value)⁻¹

theorem separatingScalarVelocity_continuousAt {frequency rootRatio : ℝ}
    (aboveRhombus : Real.sqrt 2 - 1 < rootRatio) :
    ContinuousAt (separatingScalarVelocity frequency) rootRatio := by
  have rootPositive : 0 < rootRatio := by linarith [sqrt_two_gt_one]
  unfold separatingScalarVelocity
  fun_prop (disch := positivity)

theorem separatingQuadrature_hasDerivAt {frequency rootRatio : ℝ}
    (frequencyPositive : 0 < frequency)
    (aboveRhombus : Real.sqrt 2 - 1 < rootRatio) (belowOne : rootRatio < 1) :
    HasDerivAt (separatingQuadrature frequency)
      (separatingScalarVelocity frequency rootRatio)⁻¹ rootRatio := by
  have baseAbove : Real.sqrt 2 - 1 < (1 / 2 : ℝ) := by
    linarith [sqrt_two_lt_three_halves]
  have segmentInside : Set.uIcc (1 / 2 : ℝ) rootRatio ⊆
      Set.Ioo (Real.sqrt 2 - 1) 1 := by
    intro value valueMember
    rcases Set.mem_uIcc.mp valueMember with bounds | bounds
    · exact ⟨lt_of_lt_of_le baseAbove bounds.1, lt_of_le_of_lt bounds.2 belowOne⟩
    · exact ⟨lt_of_lt_of_le aboveRhombus bounds.1, by linarith [bounds.2]⟩
  have integrandContinuous : ContinuousOn
      (fun value => (separatingScalarVelocity frequency value)⁻¹)
      (Set.Ioo (Real.sqrt 2 - 1) 1) := by
    intro value valueMember
    exact ((separatingScalarVelocity_continuousAt valueMember.1).inv₀
      (separatingScalarVelocity_pos frequency value frequencyPositive
        valueMember.1 valueMember.2).ne').continuousWithinAt
  have measurable : Measurable (fun value => (separatingScalarVelocity frequency value)⁻¹) := by
    unfold separatingScalarVelocity
    fun_prop
  exact intervalIntegral.integral_hasDerivAt_right
    (integrandContinuous.mono segmentInside).intervalIntegrable
    measurable.stronglyMeasurable.stronglyMeasurableAtFilter
    ((separatingScalarVelocity_continuousAt aboveRhombus).inv₀
      (separatingScalarVelocity_pos frequency rootRatio frequencyPositive aboveRhombus belowOne).ne')

theorem separatingQuadrature_strictMonoOn {frequency : ℝ}
    (frequencyPositive : 0 < frequency) :
    StrictMonoOn (separatingQuadrature frequency) (Set.Ioo (Real.sqrt 2 - 1) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · intro rootRatio bounds
    exact (separatingQuadrature_hasDerivAt frequencyPositive bounds.1 bounds.2).continuousAt.continuousWithinAt
  · intro rootRatio bounds
    rw [isOpen_Ioo.interior_eq] at bounds
    rw [(separatingQuadrature_hasDerivAt frequencyPositive bounds.1 bounds.2).deriv]
    exact inv_pos.mpr (separatingScalarVelocity_pos frequency rootRatio frequencyPositive bounds.1 bounds.2)

theorem separatingScalarVelocity_linear_upper_bound (frequency : ℝ) :
    ∃ bound > (0 : ℝ), ∀ rootRatio ∈ Set.Ioo (Real.sqrt 2 - 1) 1,
      separatingScalarVelocity frequency rootRatio ≤
        bound * (rootRatio - (Real.sqrt 2 - 1)) := by
  have factorContinuous : ContinuousOn (separatingScalarLinearFactor frequency)
      (Set.Icc (Real.sqrt 2 - 1) 1) := by
    intro rootRatio bounds
    have rootPositive : 0 < rootRatio := by linarith [bounds.1, sqrt_two_gt_one]
    apply ContinuousAt.continuousWithinAt
    unfold separatingScalarLinearFactor
    fun_prop (disch := positivity)
  obtain ⟨bound, boundProperty⟩ := isCompact_Icc.bddAbove_image factorContinuous
  refine ⟨max 1 bound, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro rootRatio bounds
  rw [separatingScalarVelocity_factorization, mul_comm]
  exact mul_le_mul_of_nonneg_right
    ((boundProperty (Set.mem_image_of_mem _ ⟨bounds.1.le, bounds.2.le⟩)).trans
      (le_max_right _ _)) (sub_nonneg.mpr bounds.1.le)

theorem separating_quadrature_integrand_lower_bound {frequency : ℝ}
    (frequencyPositive : 0 < frequency) :
    ∃ bound > (0 : ℝ), ∀ rootRatio ∈ Set.Ioo (Real.sqrt 2 - 1) 1,
      (bound * (rootRatio - (Real.sqrt 2 - 1)))⁻¹ ≤
        (separatingScalarVelocity frequency rootRatio)⁻¹ := by
  obtain ⟨bound, boundPositive, boundProperty⟩ :=
    separatingScalarVelocity_linear_upper_bound frequency
  refine ⟨bound, boundPositive, ?_⟩
  intro rootRatio bounds
  exact (inv_le_inv₀ (mul_pos boundPositive (sub_pos.mpr bounds.1))
    (separatingScalarVelocity_pos frequency rootRatio frequencyPositive bounds.1 bounds.2)).mpr
    (boundProperty rootRatio bounds)

end EulerNonuniqueness.Section2
