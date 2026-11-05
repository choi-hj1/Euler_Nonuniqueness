import EulerNonuniqueness.Section2.SeparatingOrbit
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section

namespace EulerNonuniqueness.Section2

theorem separatingQuadrature_log_comparison {frequency : ℝ}
    (frequencyPositive : 0 < frequency) :
    ∃ bound > (0 : ℝ), MonotoneOn
      (fun rootRatio => separatingQuadrature frequency rootRatio -
        Real.log (rootRatio - (Real.sqrt 2 - 1)) / bound)
      (Set.Ioo (Real.sqrt 2 - 1) 1) := by
  obtain ⟨bound, boundPositive, boundProperty⟩ :=
    separating_quadrature_integrand_lower_bound frequencyPositive
  refine ⟨bound, boundPositive, ?_⟩
  have derivative : ∀ rootRatio ∈ Set.Ioo (Real.sqrt 2 - 1) 1,
      HasDerivAt (fun value => separatingQuadrature frequency value -
        Real.log (value - (Real.sqrt 2 - 1)) / bound)
        ((separatingScalarVelocity frequency rootRatio)⁻¹ -
          (bound * (rootRatio - (Real.sqrt 2 - 1)))⁻¹) rootRatio := by
    intro rootRatio bounds
    convert (separatingQuadrature_hasDerivAt frequencyPositive bounds.1 bounds.2).sub
      ((((hasDerivAt_id rootRatio).sub_const (Real.sqrt 2 - 1)).log
        (sub_pos.mpr bounds.1).ne').div_const bound) using 1 <;> simp <;> ring
  apply monotoneOn_of_deriv_nonneg (convex_Ioo _ _)
  · intro rootRatio bounds
    exact (derivative rootRatio bounds).continuousAt.continuousWithinAt
  · intro rootRatio bounds
    rw [isOpen_Ioo.interior_eq] at bounds
    exact (derivative rootRatio bounds).differentiableAt.differentiableWithinAt
  · intro rootRatio bounds
    rw [isOpen_Ioo.interior_eq] at bounds
    rw [(derivative rootRatio bounds).deriv]
    exact sub_nonneg.mpr (boundProperty rootRatio bounds)

theorem separatingQuadrature_incoming_limit {frequency : ℝ}
    (frequencyPositive : 0 < frequency) :
    Filter.Tendsto (separatingQuadrature frequency)
      (nhdsWithin (Real.sqrt 2 - 1) (Set.Ioi (Real.sqrt 2 - 1))) Filter.atBot := by
  obtain ⟨bound, boundPositive, comparison⟩ :=
    separatingQuadrature_log_comparison frequencyPositive
  have baseBounds : (1 / 2 : ℝ) ∈ Set.Ioo (Real.sqrt 2 - 1) 1 := by
    constructor
    · linarith [sqrt_two_lt_three_halves]
    · norm_num
  have shiftedLimit : Filter.Tendsto (fun value : ℝ => value - (Real.sqrt 2 - 1))
      (nhdsWithin (Real.sqrt 2 - 1) (Set.Ioi (Real.sqrt 2 - 1)))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · convert (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds).sub_const (Real.sqrt 2 - 1) using 1 <;> simp
    · filter_upwards [self_mem_nhdsWithin] with value bounds
      exact sub_pos.mpr (show Real.sqrt 2 - 1 < value from bounds)
  have logarithmLimit := Real.tendsto_log_nhdsGT_zero.comp shiftedLimit
  have upperLimit := Filter.tendsto_atBot_add_const_right _
    (separatingQuadrature frequency (1 / 2) -
      Real.log ((1 / 2 : ℝ) - (Real.sqrt 2 - 1)) / bound)
    (logarithmLimit.atBot_div_const boundPositive)
  apply Filter.tendsto_atBot_mono' _ _ upperLimit
  have belowBase : ∀ᶠ value : ℝ in nhdsWithin (Real.sqrt 2 - 1)
      (Set.Ioi (Real.sqrt 2 - 1)), value < 1 / 2 :=
    (eventually_lt_nhds baseBounds.1).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, belowBase] with value lower upper
  have result := comparison ⟨lower, lt_trans upper baseBounds.2⟩ baseBounds upper.le
  dsimp at result ⊢
  linarith

theorem separatingEscapeVelocity_upper_bound (frequency : ℝ) :
    ∃ bound > (0 : ℝ), ∀ rootRatio ∈ Set.Ioo (Real.sqrt 2 - 1) 1,
      separatingEscapeVelocity frequency rootRatio ≤ bound := by
  have continuous : ContinuousOn (separatingEscapeVelocity frequency)
      (Set.Icc (Real.sqrt 2 - 1) 1) := by
    intro rootRatio bounds
    have rootPositive : 0 < rootRatio := by linarith [bounds.1, sqrt_two_gt_one]
    apply ContinuousAt.continuousWithinAt
    unfold separatingEscapeVelocity
    fun_prop (disch := positivity)
  obtain ⟨bound, boundProperty⟩ := isCompact_Icc.bddAbove_image continuous
  refine ⟨max 1 bound, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro rootRatio bounds
  exact (boundProperty (Set.mem_image_of_mem _ ⟨bounds.1.le, bounds.2.le⟩)).trans
    (le_max_right _ _)

theorem separatingEscapeCoordinate_hasDerivAt {rootRatio : ℝ}
    (aboveRhombus : Real.sqrt 2 - 1 < rootRatio) (belowOne : rootRatio < 1) :
    HasDerivAt (fun value : ℝ => (Real.sqrt (1 - value ^ 2))⁻¹)
      (rootRatio / Real.sqrt (1 - rootRatio ^ 2) ^ 3) rootRatio := by
  have rootPositive : 0 < rootRatio := by linarith [sqrt_two_gt_one]
  have endpointPositive : 0 < 1 - rootRatio ^ 2 := by nlinarith
  have radicalPositive : 0 < Real.sqrt (1 - rootRatio ^ 2) :=
    Real.sqrt_pos.mpr endpointPositive
  convert (((hasDerivAt_const rootRatio (1 : ℝ)).sub
    ((hasDerivAt_id rootRatio).pow 2)).sqrt endpointPositive.ne').inv radicalPositive.ne' using 1
  field_simp
  linear_combination -2 * rootRatio * Real.sqrt (1 - rootRatio ^ 2) *
    Real.sq_sqrt endpointPositive.le

theorem separating_escape_velocity_identity (frequency rootRatio : ℝ)
    (rootPositive : 0 < rootRatio) (belowOne : rootRatio < 1) :
    separatingScalarVelocity frequency rootRatio *
      (rootRatio / Real.sqrt (1 - rootRatio ^ 2) ^ 3) =
      separatingEscapeVelocity frequency rootRatio := by
  have radicalPositive : 0 < Real.sqrt (1 - rootRatio ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith)
  unfold separatingScalarVelocity separatingEscapeVelocity
  field_simp only [rootPositive.ne', radicalPositive.ne', pow_ne_zero]
  ring

theorem separatingQuadrature_escape_comparison {frequency : ℝ}
    (frequencyPositive : 0 < frequency) :
    ∃ bound > (0 : ℝ), MonotoneOn
      (fun rootRatio => separatingQuadrature frequency rootRatio -
        (Real.sqrt (1 - rootRatio ^ 2))⁻¹ / bound)
      (Set.Ioo (Real.sqrt 2 - 1) 1) := by
  obtain ⟨bound, boundPositive, boundProperty⟩ :=
    separatingEscapeVelocity_upper_bound frequency
  refine ⟨bound, boundPositive, ?_⟩
  have derivative : ∀ rootRatio ∈ Set.Ioo (Real.sqrt 2 - 1) 1,
      HasDerivAt (fun value => separatingQuadrature frequency value -
        (Real.sqrt (1 - value ^ 2))⁻¹ / bound)
        ((separatingScalarVelocity frequency rootRatio)⁻¹ -
          (rootRatio / Real.sqrt (1 - rootRatio ^ 2) ^ 3) / bound) rootRatio := by
    intro rootRatio bounds
    exact (separatingQuadrature_hasDerivAt frequencyPositive bounds.1 bounds.2).sub
      ((separatingEscapeCoordinate_hasDerivAt bounds.1 bounds.2).div_const bound)
  apply monotoneOn_of_deriv_nonneg (convex_Ioo _ _)
  · intro rootRatio bounds
    exact (derivative rootRatio bounds).continuousAt.continuousWithinAt
  · intro rootRatio bounds
    rw [isOpen_Ioo.interior_eq] at bounds
    exact (derivative rootRatio bounds).differentiableAt.differentiableWithinAt
  · intro rootRatio bounds
    rw [isOpen_Ioo.interior_eq] at bounds
    rw [(derivative rootRatio bounds).deriv]
    have velocityPositive := separatingScalarVelocity_pos frequency rootRatio
      frequencyPositive bounds.1 bounds.2
    have rootPositive : 0 < rootRatio := by linarith [bounds.1, sqrt_two_gt_one]
    have identity := separating_escape_velocity_identity frequency rootRatio rootPositive bounds.2
    have boundResult := boundProperty rootRatio bounds
    apply sub_nonneg.mpr
    apply (div_le_iff₀ boundPositive).mpr
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ velocityPositive).mpr
    rw [mul_comm _ (separatingScalarVelocity frequency rootRatio), identity]
    exact boundResult

theorem separatingQuadrature_outgoing_limit {frequency : ℝ}
    (frequencyPositive : 0 < frequency) :
    Filter.Tendsto (separatingQuadrature frequency)
      (nhdsWithin 1 (Set.Iio 1)) Filter.atTop := by
  obtain ⟨bound, boundPositive, comparison⟩ :=
    separatingQuadrature_escape_comparison frequencyPositive
  have baseBounds : (1 / 2 : ℝ) ∈ Set.Ioo (Real.sqrt 2 - 1) 1 := by
    constructor
    · linarith [sqrt_two_lt_three_halves]
    · norm_num
  have aboveBase : ∀ᶠ value : ℝ in nhdsWithin 1 (Set.Iio 1), 1 / 2 < value :=
    (eventually_gt_nhds (show (1 / 2 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have radicalLimit : Filter.Tendsto (fun value : ℝ => Real.sqrt (1 - value ^ 2))
      (nhdsWithin 1 (Set.Iio 1)) (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have continuous : Continuous (fun value : ℝ => Real.sqrt (1 - value ^ 2)) := by fun_prop
      convert continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> norm_num
    · filter_upwards [self_mem_nhdsWithin, aboveBase] with value upper lower
      apply Real.sqrt_pos.mpr
      have : value < 1 := upper
      nlinarith
  have escapeLimit := tendsto_inv_nhdsGT_zero.comp radicalLimit
  have lowerLimit := Filter.tendsto_atTop_add_const_right _
    (separatingQuadrature frequency (1 / 2) -
      (Real.sqrt (1 - (1 / 2 : ℝ) ^ 2))⁻¹ / bound)
    (escapeLimit.atTop_div_const boundPositive)
  apply Filter.tendsto_atTop_mono' _ _ lowerLimit
  filter_upwards [self_mem_nhdsWithin, aboveBase] with value upper lower
  have result := comparison baseBounds ⟨lt_trans baseBounds.1 lower, upper⟩ lower.le
  dsimp at result ⊢
  linarith

theorem separatingQuadrature_surjOn {frequency : ℝ}
    (frequencyPositive : 0 < frequency) :
    Set.SurjOn (separatingQuadrature frequency) (Set.Ioo (Real.sqrt 2 - 1) 1) Set.univ := by
  have endpoints : Real.sqrt 2 - 1 < (1 : ℝ) := by linarith [sqrt_two_lt_three_halves]
  apply ContinuousOn.surjOn_of_tendsto
    (show (Set.Ioo (Real.sqrt 2 - 1) (1 : ℝ)).Nonempty from
      Set.nonempty_Ioo.mpr endpoints)
  · intro rootRatio bounds
    exact (separatingQuadrature_hasDerivAt frequencyPositive bounds.1 bounds.2).continuousAt.continuousWithinAt
  · exact (tendsto_comp_coe_Ioo_atBot endpoints).mpr
      (separatingQuadrature_incoming_limit frequencyPositive)
  · exact (tendsto_comp_coe_Ioo_atTop endpoints).mpr
      (separatingQuadrature_outgoing_limit frequencyPositive)

def separatingQuadratureOrderIso (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    Set.Ioo (Real.sqrt 2 - 1) (1 : ℝ) ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (fun rootRatio => separatingQuadrature frequency rootRatio)
    (fun first second inequality => separatingQuadrature_strictMonoOn frequencyPositive
      first.property second.property inequality)
    (Set.surjOn_iff_surjective.mp (separatingQuadrature_surjOn frequencyPositive))

def separatingScalarOrbit (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) : ℝ :=
  ((separatingQuadratureOrderIso frequency frequencyPositive).symm time : ℝ)

theorem separatingScalarOrbit_mem (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    separatingScalarOrbit frequency frequencyPositive time ∈ Set.Ioo (Real.sqrt 2 - 1) 1 :=
  ((separatingQuadratureOrderIso frequency frequencyPositive).symm time).property

theorem separatingQuadrature_scalarOrbit (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    separatingQuadrature frequency (separatingScalarOrbit frequency frequencyPositive time) = time := by
  exact (separatingQuadratureOrderIso frequency frequencyPositive).apply_symm_apply time

theorem separatingScalarOrbit_continuous (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    Continuous (separatingScalarOrbit frequency frequencyPositive) :=
  continuous_subtype_val.comp (separatingQuadratureOrderIso frequency frequencyPositive).symm.continuous

theorem separatingScalarOrbit_hasDerivAt (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    HasDerivAt (separatingScalarOrbit frequency frequencyPositive)
      (separatingScalarVelocity frequency (separatingScalarOrbit frequency frequencyPositive time)) time := by
  have bounds := separatingScalarOrbit_mem frequency frequencyPositive time
  have velocityPositive := separatingScalarVelocity_pos frequency _ frequencyPositive bounds.1 bounds.2
  convert HasDerivAt.of_local_left_inverse
    (separatingScalarOrbit_continuous frequency frequencyPositive).continuousAt
    (separatingQuadrature_hasDerivAt frequencyPositive bounds.1 bounds.2)
    (inv_ne_zero velocityPositive.ne')
    (Filter.Eventually.of_forall (separatingQuadrature_scalarOrbit frequency frequencyPositive)) using 1
  exact (inv_inv _).symm

theorem separatingScalarOrbit_incoming_limit (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    Filter.Tendsto (separatingScalarOrbit frequency frequencyPositive) Filter.atBot
      (nhds (Real.sqrt 2 - 1)) := by
  exact ((tendsto_Ioo_atBot.mp
    (separatingQuadratureOrderIso frequency frequencyPositive).symm.tendsto_atBot)).mono_right
    nhdsWithin_le_nhds

theorem separatingScalarOrbit_outgoing_limit (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    Filter.Tendsto (separatingScalarOrbit frequency frequencyPositive) Filter.atTop (nhds 1) := by
  exact ((tendsto_Ioo_atTop.mp
    (separatingQuadratureOrderIso frequency frequencyPositive).symm.tendsto_atTop)).mono_right
    nhdsWithin_le_nhds

theorem separatingScalarOrbit_strictMono (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    StrictMono (separatingScalarOrbit frequency frequencyPositive) := by
  intro first second inequality
  exact (separatingQuadratureOrderIso frequency frequencyPositive).symm.strictMono inequality

theorem exists_right_limit_of_bounded_derivative {function derivative : ℝ → ℝ}
    {left right bound : ℝ} (endpoints : left < right) (boundNonnegative : 0 ≤ bound)
    (derivativeProperty : ∀ value ∈ Set.Ioo left right, HasDerivAt function (derivative value) value)
    (boundProperty : ∀ value ∈ Set.Ioo left right, ‖derivative value‖ ≤ bound) :
    ∃ limit : ℝ, Filter.Tendsto function (nhdsWithin left (Set.Ioi left)) (nhds limit) := by
  have lipschitz : LipschitzOnWith ⟨bound, boundNonnegative⟩ function (Set.Ioo left right) := by
    apply (convex_Ioo left right).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun value bounds => (derivativeProperty value bounds).hasDerivWithinAt)
    intro value bounds
    exact_mod_cast boundProperty value bounds
  obtain ⟨extension, extensionLipschitz, extensionEqual⟩ := lipschitz.extend_real
  refine ⟨extension left, ?_⟩
  have equality : extension =ᶠ[nhdsWithin left (Set.Ioi left)] function := by
    have upper : ∀ᶠ value : ℝ in nhdsWithin left (Set.Ioi left), value < right :=
      (eventually_lt_nhds endpoints).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, upper] with value lower upper
    exact (extensionEqual ⟨lower, upper⟩).symm
  exact (extensionLipschitz.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' equality

theorem separatingScalarLinearFactor_differentiableAt_rhombus (frequency : ℝ) :
    DifferentiableAt ℝ (separatingScalarLinearFactor frequency) (Real.sqrt 2 - 1) := by
  have rootPositive : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_gt_one]
  have firstPositive : 0 < 1 - (Real.sqrt 2 - 1) ^ 2 := by
    nlinarith [sqrt_two_lt_three_halves, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have secondPositive : 0 < (Real.sqrt 2 - 1) ^ 2 + 4 * (Real.sqrt 2 - 1) - 1 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have firstDerivative := ((hasDerivAt_const (Real.sqrt 2 - 1) (1 : ℝ)).sub
    ((hasDerivAt_id _).pow 2)).sqrt firstPositive.ne'
  have secondDerivative := ((((hasDerivAt_id (Real.sqrt 2 - 1)).pow 2).add
    ((hasDerivAt_id _).const_mul 4)).sub_const 1).sqrt secondPositive.ne'
  unfold separatingScalarLinearFactor
  exact (((differentiableAt_const _).mul (firstDerivative.differentiableAt.pow 3)).div
    (differentiableAt_id.pow 2) (pow_ne_zero 2 rootPositive.ne')).mul
    (((differentiableAt_id.add_const _).add_const _)) |>.mul secondDerivative.differentiableAt

theorem regularized_inverse_eventually_bounded {factor : ℝ → ℝ} {endpoint rate : ℝ}
    (ratePositive : 0 < rate) (factorValue : factor endpoint = rate)
    (factorDifferentiable : DifferentiableAt ℝ factor endpoint) :
    ∃ bound > (0 : ℝ), ∀ᶠ value in nhds endpoint, value ≠ endpoint →
      ‖((value - endpoint) * factor value)⁻¹ - (rate * (value - endpoint))⁻¹‖ ≤ bound := by
  obtain ⟨constant, constantPositive, differenceBound⟩ :=
    factorDifferentiable.hasDerivAt.isBigO_sub.exists_pos
  have factorLower : ∀ᶠ value in nhds endpoint, rate / 2 < factor value := by
    have result := factorDifferentiable.continuousAt.eventually
      (eventually_gt_nhds (show rate / 2 < factor endpoint by rw [factorValue]; linarith))
    exact result
  refine ⟨2 * constant / rate ^ 2, by positivity, ?_⟩
  filter_upwards [differenceBound.bound, factorLower] with value differenceBound factorLower
  intro valueNe
  have factorPositive : 0 < factor value := by linarith
  have differencePositive : 0 < |value - endpoint| := abs_pos.mpr (sub_ne_zero.mpr valueNe)
  have identity : ((value - endpoint) * factor value)⁻¹ - (rate * (value - endpoint))⁻¹ =
      (rate - factor value) / (rate * (value - endpoint) * factor value) := by
    field_simp [sub_ne_zero.mpr valueNe, ratePositive.ne', factorPositive.ne']
    <;> ring
  rw [identity, Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
    abs_of_pos ratePositive, abs_of_pos factorPositive, abs_sub_comm]
  have numeratorBound : |factor value - rate| / |value - endpoint| ≤ constant := by
    apply (div_le_iff₀ differencePositive).mpr
    simpa only [factorValue, Real.norm_eq_abs] using differenceBound
  calc
    _ = (|factor value - rate| / |value - endpoint|) / (rate * factor value) := by
      rw [div_div]
      congr 1
      ring
    _ ≤ constant / (rate * factor value) :=
      div_le_div_of_nonneg_right numeratorBound (mul_pos ratePositive factorPositive).le
    _ ≤ constant / (rate ^ 2 / 2) := by
      apply div_le_div_of_nonneg_left constantPositive.le (by positivity)
      nlinarith
    _ = _ := by field_simp; ring

def separatingRegularizedQuadrature (frequency rootRatio : ℝ) : ℝ :=
  separatingQuadrature frequency rootRatio -
    Real.log (rootRatio - (Real.sqrt 2 - 1)) / (2 * Real.sqrt 2 * frequency)

theorem separatingRegularizedQuadrature_hasDerivAt {frequency rootRatio : ℝ}
    (frequencyPositive : 0 < frequency)
    (aboveRhombus : Real.sqrt 2 - 1 < rootRatio) (belowOne : rootRatio < 1) :
    HasDerivAt (separatingRegularizedQuadrature frequency)
      ((separatingScalarVelocity frequency rootRatio)⁻¹ -
        ((2 * Real.sqrt 2 * frequency) * (rootRatio - (Real.sqrt 2 - 1)))⁻¹) rootRatio := by
  convert (separatingQuadrature_hasDerivAt frequencyPositive aboveRhombus belowOne).sub
    ((((hasDerivAt_id rootRatio).sub_const (Real.sqrt 2 - 1)).log
      (sub_pos.mpr aboveRhombus).ne').div_const (2 * Real.sqrt 2 * frequency)) using 1 <;>
    simp [separatingRegularizedQuadrature] <;> ring

theorem separatingRegularizedQuadrature_incoming_limit {frequency : ℝ}
    (frequencyPositive : 0 < frequency) :
    ∃ limit : ℝ, Filter.Tendsto (separatingRegularizedQuadrature frequency)
      (nhdsWithin (Real.sqrt 2 - 1) (Set.Ioi (Real.sqrt 2 - 1))) (nhds limit) := by
  have ratePositive : 0 < 2 * Real.sqrt 2 * frequency := by positivity
  obtain ⟨bound, boundPositive, localBound⟩ := regularized_inverse_eventually_bounded
    ratePositive (separatingScalarLinearFactor_at_rhombus frequency)
    (separatingScalarLinearFactor_differentiableAt_rhombus frequency)
  obtain ⟨radius, radiusPositive, radiusProperty⟩ := Metric.eventually_nhds_iff.mp localBound
  have endpointGap : 0 < 1 - (Real.sqrt 2 - 1) := by linarith [sqrt_two_lt_three_halves]
  have smallPositive : 0 < min radius (1 - (Real.sqrt 2 - 1)) := lt_min radiusPositive endpointGap
  apply exists_right_limit_of_bounded_derivative
    (right := Real.sqrt 2 - 1 + min radius (1 - (Real.sqrt 2 - 1)))
    (bound := bound) (by linarith) boundPositive.le
    (derivative := fun value => (separatingScalarVelocity frequency value)⁻¹ -
      ((2 * Real.sqrt 2 * frequency) * (value - (Real.sqrt 2 - 1)))⁻¹)
  · intro value bounds
    apply separatingRegularizedQuadrature_hasDerivAt frequencyPositive bounds.1
    have := min_le_right radius (1 - (Real.sqrt 2 - 1))
    linarith [bounds.2]
  · intro value bounds
    rw [separatingScalarVelocity_factorization]
    apply radiusProperty _ (ne_of_gt bounds.1)
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr bounds.1)]
    have := min_le_left radius (1 - (Real.sqrt 2 - 1))
    linarith [bounds.2]

theorem separatingScalarOrbit_incoming_exponential (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    ∃ coefficient > (0 : ℝ), Filter.Tendsto
      (fun time => Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
        (separatingScalarOrbit frequency frequencyPositive time - (Real.sqrt 2 - 1)))
      Filter.atBot (nhds coefficient) := by
  obtain ⟨limit, limitProperty⟩ := separatingRegularizedQuadrature_incoming_limit frequencyPositive
  refine ⟨Real.exp (-(2 * Real.sqrt 2 * frequency) * limit), Real.exp_pos _, ?_⟩
  have scalarWithin := tendsto_Ioo_atBot.mp
    (separatingQuadratureOrderIso frequency frequencyPositive).symm.tendsto_atBot
  have regularizedLimit := limitProperty.comp scalarWithin
  have result := Real.continuous_exp.continuousAt.tendsto.comp
    (regularizedLimit.const_mul (-(2 * Real.sqrt 2 * frequency)))
  apply result.congr'
  apply Filter.Eventually.of_forall
  intro time
  have bounds := separatingScalarOrbit_mem frequency frequencyPositive time
  have exponentIdentity : -(2 * Real.sqrt 2 * frequency) *
      separatingRegularizedQuadrature frequency (separatingScalarOrbit frequency frequencyPositive time) =
      -(2 * Real.sqrt 2 * frequency) * time +
        Real.log (separatingScalarOrbit frequency frequencyPositive time - (Real.sqrt 2 - 1)) := by
    rw [separatingRegularizedQuadrature, separatingQuadrature_scalarOrbit]
    field_simp
    <;> ring
  change Real.exp (-(2 * Real.sqrt 2 * frequency) *
    separatingRegularizedQuadrature frequency (separatingScalarOrbit frequency frequencyPositive time)) = _
  rw [exponentIdentity, Real.exp_add, Real.exp_log (sub_pos.mpr bounds.1)]

theorem separatingScalarOrbit_quadrature (frequency : ℝ) (frequencyPositive : 0 < frequency)
    {rootRatio : ℝ} (bounds : rootRatio ∈ Set.Ioo (Real.sqrt 2 - 1) 1) :
    separatingScalarOrbit frequency frequencyPositive (separatingQuadrature frequency rootRatio) = rootRatio := by
  have equality := (separatingQuadratureOrderIso frequency frequencyPositive).symm_apply_apply
    (⟨rootRatio, bounds⟩ : Set.Ioo (Real.sqrt 2 - 1) (1 : ℝ))
  exact congrArg Subtype.val equality

theorem removable_quotient_eventually_bounded {numerator factor : ℝ → ℝ} {endpoint rate : ℝ}
    (ratePositive : 0 < rate) (factorValue : factor endpoint = rate)
    (factorContinuous : ContinuousAt factor endpoint) (numeratorValue : numerator endpoint = 0)
    (numeratorDifferentiable : DifferentiableAt ℝ numerator endpoint) :
    ∃ bound > (0 : ℝ), ∀ᶠ value in nhds endpoint, value ≠ endpoint →
      ‖numerator value / ((value - endpoint) * factor value)‖ ≤ bound := by
  obtain ⟨constant, constantPositive, differenceBound⟩ :=
    numeratorDifferentiable.hasDerivAt.isBigO_sub.exists_pos
  have factorLower : ∀ᶠ value in nhds endpoint, rate / 2 < factor value := by
    exact factorContinuous.eventually
      (eventually_gt_nhds (show rate / 2 < factor endpoint by rw [factorValue]; linarith))
  refine ⟨2 * constant / rate, by positivity, ?_⟩
  filter_upwards [differenceBound.bound, factorLower] with value differenceBound factorLower
  intro valueNe
  have factorPositive : 0 < factor value := by linarith
  have differencePositive : 0 < |value - endpoint| := abs_pos.mpr (sub_ne_zero.mpr valueNe)
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos factorPositive]
  have quotientBound : ‖numerator value‖ / |value - endpoint| ≤ constant := by
    apply (div_le_iff₀ differencePositive).mpr
    simpa only [numeratorValue, sub_zero, Real.norm_eq_abs] using differenceBound
  calc
    _ = (|numerator value| / |value - endpoint|) / factor value := (div_div _ _ _).symm
    _ ≤ constant / factor value := div_le_div_of_nonneg_right quotientBound factorPositive.le
    _ ≤ constant / (rate / 2) := div_le_div_of_nonneg_left constantPositive.le (by positivity) factorLower.le
    _ = _ := by field_simp; ring

def separatingEscapeCoordinate (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) : ℝ :=
  (Real.sqrt (1 - separatingScalarOrbit frequency frequencyPositive time ^ 2))⁻¹

theorem separatingEscapeCoordinate_trajectory_hasDerivAt (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    HasDerivAt (separatingEscapeCoordinate frequency frequencyPositive)
      (separatingEscapeVelocity frequency (separatingScalarOrbit frequency frequencyPositive time)) time := by
  have bounds := separatingScalarOrbit_mem frequency frequencyPositive time
  have rootPositive : 0 < separatingScalarOrbit frequency frequencyPositive time := by
    linarith [bounds.1, sqrt_two_gt_one]
  exact separating_escape_coordinate_derivative rootPositive bounds.2
    (separatingScalarOrbit_hasDerivAt frequency frequencyPositive time)

theorem separatingEscapeCoordinate_pos (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    0 < separatingEscapeCoordinate frequency frequencyPositive time := by
  have bounds := separatingScalarOrbit_mem frequency frequencyPositive time
  have rootPositive : 0 < separatingScalarOrbit frequency frequencyPositive time := by
    linarith [bounds.1, sqrt_two_gt_one]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by nlinarith [bounds.2]))

theorem separatingEscapeCoordinate_linear_lower (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    ∃ timeMin > (0 : ℝ), ∀ time, timeMin ≤ time →
      frequency / 4 * time ≤ separatingEscapeCoordinate frequency frequencyPositive time := by
  have velocityLimit := separating_escape_coordinate_velocity_limit (frequency := frequency)
    (separatingScalarOrbit_outgoing_limit frequency frequencyPositive)
  have eventualLower : ∀ᶠ time in Filter.atTop,
      frequency / 2 ≤ separatingEscapeVelocity frequency (separatingScalarOrbit frequency frequencyPositive time) :=
    velocityLimit.eventually (eventually_ge_nhds (by linarith : frequency / 2 < frequency))
  obtain ⟨threshold, thresholdProperty⟩ := Filter.eventually_atTop.mp eventualLower
  let base := max 1 threshold
  have basePositive : 0 < base := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have baseAbove : threshold ≤ base := le_max_right _ _
  have derivative : ∀ time ∈ Set.Ici base,
      HasDerivAt (fun currentTime => separatingEscapeCoordinate frequency frequencyPositive currentTime -
        frequency / 2 * currentTime)
        (separatingEscapeVelocity frequency (separatingScalarOrbit frequency frequencyPositive time) - frequency / 2) time := by
    intro time _
    simpa only [id_eq, mul_one] using (separatingEscapeCoordinate_trajectory_hasDerivAt frequency frequencyPositive time).sub
      ((hasDerivAt_id time).const_mul (frequency / 2))
  have monotonicity : MonotoneOn (fun time => separatingEscapeCoordinate frequency frequencyPositive time -
      frequency / 2 * time) (Set.Ici base) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · intro time bounds
      exact (derivative time bounds).continuousAt.continuousWithinAt
    · intro time bounds
      exact (derivative time (interior_subset bounds)).differentiableAt.differentiableWithinAt
    · intro time bounds
      rw [(derivative time (interior_subset bounds)).deriv]
      exact sub_nonneg.mpr (thresholdProperty time (baseAbove.trans (interior_subset bounds)))
  refine ⟨2 * base, by positivity, ?_⟩
  intro time timeAbove
  have baseLeTime : base ≤ time := by linarith
  have comparison := monotonicity (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr baseLeTime) baseLeTime
  have baseCoordinatePositive := separatingEscapeCoordinate_pos frequency frequencyPositive base
  nlinarith

theorem exists_complex_right_limit_of_bounded_derivative {function derivative : ℝ → ℂ}
    {left right bound : ℝ} (endpoints : left < right) (boundNonnegative : 0 ≤ bound)
    (derivativeProperty : ∀ value ∈ Set.Ioo left right, HasDerivAt function (derivative value) value)
    (boundProperty : ∀ value ∈ Set.Ioo left right, ‖derivative value‖ ≤ bound) :
    ∃ limit : ℂ, Filter.Tendsto function (nhdsWithin left (Set.Ioi left)) (nhds limit) := by
  have lipschitz : LipschitzOnWith ⟨bound, boundNonnegative⟩ function (Set.Ioo left right) := by
    apply (convex_Ioo left right).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun value bounds => (derivativeProperty value bounds).hasDerivWithinAt)
    intro value bounds
    exact_mod_cast boundProperty value bounds
  obtain ⟨extension, extensionLipschitz, extensionEqual⟩ := lipschitz.extend_finite_dimension
  refine ⟨extension left, ?_⟩
  have equality : extension =ᶠ[nhdsWithin left (Set.Ioi left)] function := by
    have upper : ∀ᶠ value : ℝ in nhdsWithin left (Set.Ioi left), value < right :=
      (eventually_lt_nhds endpoints).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, upper] with value lower upper
    exact (extensionEqual ⟨lower, upper⟩).symm
  exact (extensionLipschitz.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' equality

theorem complex_right_limit_quadratic_error {function derivative : ℝ → ℂ} {right bound : ℝ}
    (rightPositive : 0 < right) (boundNonnegative : 0 ≤ bound)
    (derivativeProperty : ∀ value ∈ Set.Ioo 0 right, HasDerivAt function (derivative value) value)
    (boundProperty : ∀ value ∈ Set.Ioo 0 right, ‖derivative value‖ ≤ bound * value) :
    ∃ limit : ℂ, Filter.Tendsto function (nhdsWithin 0 (Set.Ioi 0)) (nhds limit) ∧
      ∀ value ∈ Set.Ioo 0 right, ‖function value - limit‖ ≤ bound * value ^ 2 := by
  obtain ⟨limit, limitProperty⟩ := exists_complex_right_limit_of_bounded_derivative rightPositive
    (mul_nonneg boundNonnegative rightPositive.le) derivativeProperty
    (fun value bounds => (boundProperty value bounds).trans
      (mul_le_mul_of_nonneg_left bounds.2.le boundNonnegative))
  refine ⟨limit, limitProperty, ?_⟩
  intro value bounds
  have constantLimit : Filter.Tendsto (fun _ : ℝ => function value)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (function value)) := tendsto_const_nhds
  have normLimit := (constantLimit.sub limitProperty).norm
  have scalarLimit : Filter.Tendsto (fun smaller : ℝ => bound * value * ‖value - smaller‖)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (bound * value ^ 2)) := by
    have continuous : Continuous (fun smaller : ℝ => bound * value * ‖value - smaller‖) := by fun_prop
    convert continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
    simp [abs_of_pos bounds.1, Real.norm_eq_abs]
    <;> ring
  apply le_of_tendsto_of_tendsto normLimit scalarLimit
  have below : ∀ᶠ smaller : ℝ in nhdsWithin 0 (Set.Ioi 0), smaller < value :=
    (eventually_lt_nhds bounds.1).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, below] with smaller smallerPositive smallerBelow
  have segmentInside : Set.Icc smaller value ⊆ Set.Ioo 0 right := by
    intro current currentBounds
    exact ⟨lt_of_lt_of_le smallerPositive currentBounds.1, lt_of_le_of_lt currentBounds.2 bounds.2⟩
  exact (convex_Icc smaller value).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun current currentBounds => (derivativeProperty current (segmentInside currentBounds)).hasDerivWithinAt)
    (fun current currentBounds => (boundProperty current (segmentInside currentBounds)).trans
      (mul_le_mul_of_nonneg_left currentBounds.2 boundNonnegative))
    (Set.mem_Icc.mpr ⟨le_rfl, smallerBelow.le⟩) (Set.mem_Icc.mpr ⟨smallerBelow.le, le_rfl⟩)

theorem complex_right_limit_linear_error {function derivative : ℝ → ℂ} {right bound : ℝ}
    (rightPositive : 0 < right) (boundNonnegative : 0 ≤ bound)
    (derivativeProperty : ∀ value ∈ Set.Ioo 0 right, HasDerivAt function (derivative value) value)
    (boundProperty : ∀ value ∈ Set.Ioo 0 right, ‖derivative value‖ ≤ bound) :
    ∃ limit : ℂ, Filter.Tendsto function (nhdsWithin 0 (Set.Ioi 0)) (nhds limit) ∧
      ∀ value ∈ Set.Ioo 0 right, ‖function value - limit‖ ≤ bound * value := by
  obtain ⟨limit, limitProperty⟩ := exists_complex_right_limit_of_bounded_derivative
    rightPositive boundNonnegative derivativeProperty boundProperty
  refine ⟨limit, limitProperty, ?_⟩
  intro value bounds
  have constantLimit : Filter.Tendsto (fun _ : ℝ => function value)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (function value)) := tendsto_const_nhds
  have normLimit := (constantLimit.sub limitProperty).norm
  have scalarLimit : Filter.Tendsto (fun smaller : ℝ => bound * ‖value - smaller‖)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (bound * value)) := by
    have continuous : Continuous (fun smaller : ℝ => bound * ‖value - smaller‖) := by fun_prop
    convert continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
    simp [abs_of_pos bounds.1, Real.norm_eq_abs]
  apply le_of_tendsto_of_tendsto normLimit scalarLimit
  have below : ∀ᶠ smaller : ℝ in nhdsWithin 0 (Set.Ioi 0), smaller < value :=
    (eventually_lt_nhds bounds.1).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, below] with smaller smallerPositive smallerBelow
  have segmentInside : Set.Icc smaller value ⊆ Set.Ioo 0 right := by
    intro current currentBounds
    exact ⟨lt_of_lt_of_le smallerPositive currentBounds.1, lt_of_le_of_lt currentBounds.2 bounds.2⟩
  exact (convex_Icc smaller value).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun current currentBounds => (derivativeProperty current (segmentInside currentBounds)).hasDerivWithinAt)
    (fun current currentBounds => boundProperty current (segmentInside currentBounds))
    (Set.mem_Icc.mpr ⟨le_rfl, smallerBelow.le⟩) (Set.mem_Icc.mpr ⟨smallerBelow.le, le_rfl⟩)

theorem complex_atTop_quadratic_error {function derivative : ℝ → ℂ} {timeMin bound : ℝ}
    (timePositive : 0 < timeMin) (boundNonnegative : 0 ≤ bound)
    (derivativeProperty : ∀ time, timeMin < time → HasDerivAt function (derivative time) time)
    (boundProperty : ∀ time, timeMin < time → ‖derivative time‖ ≤ bound / time ^ 3) :
    ∃ limit : ℂ, Filter.Tendsto function Filter.atTop (nhds limit) ∧
      ∀ time, timeMin < time → ‖function time - limit‖ ≤ bound / time ^ 2 := by
  have reciprocalBounds : ∀ value ∈ Set.Ioo 0 timeMin⁻¹, timeMin < value⁻¹ := by
    intro value bounds
    simpa only [inv_inv] using
      (inv_lt_inv₀ (inv_pos.mpr timePositive) bounds.1).mpr bounds.2
  have transformedDerivative : ∀ value ∈ Set.Ioo 0 timeMin⁻¹,
      HasDerivAt (fun current => function current⁻¹) (-(value ^ 2)⁻¹ • derivative value⁻¹) value := by
    intro value bounds
    convert (derivativeProperty value⁻¹ (reciprocalBounds value bounds)).scomp value
      ((hasDerivAt_id value).inv bounds.1.ne') using 1
    simp [div_eq_mul_inv]
  have transformedBound : ∀ value ∈ Set.Ioo 0 timeMin⁻¹,
      ‖-(value ^ 2)⁻¹ • derivative value⁻¹‖ ≤ bound * value := by
    intro value bounds
    calc
      _ = (value ^ 2)⁻¹ * ‖derivative value⁻¹‖ := by
        simp [norm_smul, Real.norm_eq_abs, abs_of_pos bounds.1]
      _ ≤ (value ^ 2)⁻¹ * (bound / (value⁻¹) ^ 3) :=
        mul_le_mul_of_nonneg_left (boundProperty value⁻¹ (reciprocalBounds value bounds)) (by positivity)
      _ = _ := by field_simp [bounds.1.ne']; ring
  obtain ⟨limit, limitProperty, errorProperty⟩ := complex_right_limit_quadratic_error
    (inv_pos.mpr timePositive) boundNonnegative transformedDerivative transformedBound
  refine ⟨limit, ?_, ?_⟩
  · simpa only [Function.comp_def, inv_inv] using limitProperty.comp tendsto_inv_atTop_nhdsGT_zero
  · intro time timeAbove
    have positive : 0 < time := timePositive.trans timeAbove
    have reciprocalMember : time⁻¹ ∈ Set.Ioo 0 timeMin⁻¹ :=
      ⟨inv_pos.mpr positive, (inv_lt_inv₀ positive timePositive).mpr timeAbove⟩
    simpa only [inv_inv, inv_pow, div_eq_mul_inv] using errorProperty time⁻¹ reciprocalMember

theorem complex_atTop_linear_error {function derivative : ℝ → ℂ} {timeMin bound : ℝ}
    (timePositive : 0 < timeMin) (boundNonnegative : 0 ≤ bound)
    (derivativeProperty : ∀ time, timeMin < time → HasDerivAt function (derivative time) time)
    (boundProperty : ∀ time, timeMin < time → ‖derivative time‖ ≤ bound / time ^ 2) :
    ∃ limit : ℂ, Filter.Tendsto function Filter.atTop (nhds limit) ∧
      ∀ time, timeMin < time → ‖function time - limit‖ ≤ bound / time := by
  have reciprocalBounds : ∀ value ∈ Set.Ioo 0 timeMin⁻¹, timeMin < value⁻¹ := by
    intro value bounds
    simpa only [inv_inv] using
      (inv_lt_inv₀ (inv_pos.mpr timePositive) bounds.1).mpr bounds.2
  have transformedDerivative : ∀ value ∈ Set.Ioo 0 timeMin⁻¹,
      HasDerivAt (fun current => function current⁻¹) (-(value ^ 2)⁻¹ • derivative value⁻¹) value := by
    intro value bounds
    convert (derivativeProperty value⁻¹ (reciprocalBounds value bounds)).scomp value
      ((hasDerivAt_id value).inv bounds.1.ne') using 1
    simp [div_eq_mul_inv]
  have transformedBound : ∀ value ∈ Set.Ioo 0 timeMin⁻¹,
      ‖-(value ^ 2)⁻¹ • derivative value⁻¹‖ ≤ bound := by
    intro value bounds
    calc
      _ = (value ^ 2)⁻¹ * ‖derivative value⁻¹‖ := by
        simp [norm_smul, Real.norm_eq_abs, abs_of_pos bounds.1]
      _ ≤ (value ^ 2)⁻¹ * (bound / (value⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_left (boundProperty value⁻¹ (reciprocalBounds value bounds)) (by positivity)
      _ = _ := by field_simp [bounds.1.ne']
  obtain ⟨limit, limitProperty, errorProperty⟩ := complex_right_limit_linear_error
    (inv_pos.mpr timePositive) boundNonnegative transformedDerivative transformedBound
  refine ⟨limit, ?_, ?_⟩
  · simpa only [Function.comp_def, inv_inv] using limitProperty.comp tendsto_inv_atTop_nhdsGT_zero
  · intro time timeAbove
    have positive : 0 < time := timePositive.trans timeAbove
    have reciprocalMember : time⁻¹ ∈ Set.Ioo 0 timeMin⁻¹ :=
      ⟨inv_pos.mpr positive, (inv_lt_inv₀ positive timePositive).mpr timeAbove⟩
    simpa only [inv_inv, div_eq_mul_inv] using errorProperty time⁻¹ reciprocalMember

end EulerNonuniqueness.Section2
