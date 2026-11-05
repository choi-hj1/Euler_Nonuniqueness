import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set
open scoped BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

noncomputable section

abbrev HolderLabelPairs := {pair : ℝ × ℝ // pair.1 ≠ pair.2}

abbrev HolderGraphAmbient := (ℝ →ᵇ ℂ) × (HolderLabelPairs →ᵇ ℂ)

def periodicHolderGraph : Submodule ℝ HolderGraphAmbient where
  carrier := {data | (∀ pair : HolderLabelPairs,
      (Real.sqrt |pair.val.1 - pair.val.2| : ℂ) * data.2 pair =
        data.1 pair.val.1 - data.1 pair.val.2) ∧
    ∀ label : ℝ, data.1 (label + 2 * Real.pi) = data.1 label}
  zero_mem' := by simp
  add_mem' := by
    intro first second first_mem second_mem
    constructor
    · intro pair
      change _ * (first.2 pair + second.2 pair) =
        (first.1 pair.val.1 + second.1 pair.val.1) - (first.1 pair.val.2 + second.1 pair.val.2)
      rw [mul_add, first_mem.1 pair, second_mem.1 pair]
      ring
    · intro label
      change first.1 _ + second.1 _ = first.1 _ + second.1 _
      rw [first_mem.2 label, second_mem.2 label]
  smul_mem' := by
    intro scalar data membership
    constructor
    · intro pair
      change _ * (scalar • data.2 pair) = scalar • data.1 pair.val.1 - scalar • data.1 pair.val.2
      rw [mul_smul_comm, membership.1 pair, smul_sub]
    · intro label
      change scalar • data.1 _ = scalar • data.1 _
      rw [membership.2 label]

theorem periodicHolderGraph_isClosed : IsClosed (periodicHolderGraph : Set HolderGraphAmbient) := by
  change IsClosed {data : HolderGraphAmbient |
    (∀ pair : HolderLabelPairs, (Real.sqrt |pair.val.1 - pair.val.2| : ℂ) * data.2 pair =
      data.1 pair.val.1 - data.1 pair.val.2) ∧
    ∀ label : ℝ, data.1 (label + 2 * Real.pi) = data.1 label}
  apply IsClosed.inter
  · have closed : ∀ pair : HolderLabelPairs, IsClosed {data : HolderGraphAmbient |
        (Real.sqrt |pair.val.1 - pair.val.2| : ℂ) * data.2 pair =
          data.1 pair.val.1 - data.1 pair.val.2} := by
      intro pair
      exact isClosed_eq
        (continuous_const.mul ((BoundedContinuousFunction.continuous_eval_const).comp continuous_snd))
        (((BoundedContinuousFunction.continuous_eval_const).comp continuous_fst).sub
          ((BoundedContinuousFunction.continuous_eval_const).comp continuous_fst))
    convert isClosed_iInter closed using 1
    ext data
    simp
    rfl
  · have closed : ∀ label : ℝ, IsClosed {data : HolderGraphAmbient |
        data.1 (label + 2 * Real.pi) = data.1 label} := by
      intro label
      exact isClosed_eq
        ((BoundedContinuousFunction.continuous_eval_const).comp continuous_fst)
        ((BoundedContinuousFunction.continuous_eval_const).comp continuous_fst)
    convert isClosed_iInter closed using 1
    ext data
    simp
    rfl

abbrev PeriodicHolderHalf := periodicHolderGraph

noncomputable instance : CompleteSpace PeriodicHolderHalf := periodicHolderGraph_isClosed.completeSpace_coe

theorem PeriodicHolderHalf.value_bound (data : PeriodicHolderHalf) (label : ℝ) :
    ‖data.val.1 label‖ ≤ ‖data‖ := by
  exact (data.val.1.norm_coe_le_norm label).trans (le_max_left _ _)

theorem PeriodicHolderHalf.holder_bound (data : PeriodicHolderHalf) (first second : ℝ) :
    ‖data.val.1 first - data.val.1 second‖ ≤ ‖data‖ * Real.sqrt |first - second| := by
  by_cases equal : first = second
  · subst second
    simp
  let pair : HolderLabelPairs := ⟨(first, second), equal⟩
  have identity := data.property.1 pair
  change (Real.sqrt |first - second| : ℂ) * data.val.2 pair = _ at identity
  rw [← identity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have quotient_bound : ‖data.val.2 pair‖ ≤ ‖data‖ :=
    (data.val.2.norm_coe_le_norm pair).trans (le_max_right _ _)
  calc
    _ ≤ Real.sqrt |first - second| * ‖data‖ :=
      mul_le_mul_of_nonneg_left quotient_bound (Real.sqrt_nonneg _)
    _ = _ := mul_comm _ _

theorem PeriodicHolderHalf.periodic (data : PeriodicHolderHalf) :
    Function.Periodic data.val.1 (2 * Real.pi) := data.property.2

def holderDividedDifference (function : ℝ → ℂ) (pair : HolderLabelPairs) : ℂ :=
  (function pair.val.1 - function pair.val.2) / (Real.sqrt |pair.val.1 - pair.val.2| : ℂ)

theorem holderDividedDifference_continuous {function : ℝ → ℂ} (continuous : Continuous function) :
    Continuous (holderDividedDifference function) := by
  apply ((continuous.comp (continuous_fst.comp continuous_subtype_val)).sub
    (continuous.comp (continuous_snd.comp continuous_subtype_val))).div
    (Complex.continuous_ofReal.comp
      (((continuous_fst.comp continuous_subtype_val).sub
        (continuous_snd.comp continuous_subtype_val)).abs.sqrt))
  intro pair
  dsimp only [Function.comp_apply]
  exact_mod_cast (Real.sqrt_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr pair.property))).ne'

theorem holderDividedDifference_bound {function : ℝ → ℂ} {holder : ℝ}
    (estimate : ∀ first second : ℝ,
      ‖function first - function second‖ ≤ holder * Real.sqrt |first - second|)
    (pair : HolderLabelPairs) : ‖holderDividedDifference function pair‖ ≤ holder := by
  have root_pos := Real.sqrt_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr pair.property))
  rw [holderDividedDifference, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos root_pos]
  exact (div_le_iff₀ root_pos).mpr (estimate _ _)

def PeriodicHolderHalf.ofFunction (function : ℝ → ℂ) (continuous : Continuous function)
    (valueBound holder : ℝ) (value_bound : ∀ label, ‖function label‖ ≤ valueBound)
    (holder_bound : ∀ first second : ℝ,
      ‖function first - function second‖ ≤ holder * Real.sqrt |first - second|)
    (periodic : Function.Periodic function (2 * Real.pi)) : PeriodicHolderHalf :=
  ⟨(BoundedContinuousFunction.ofNormedAddCommGroup function continuous valueBound value_bound,
    BoundedContinuousFunction.ofNormedAddCommGroup (holderDividedDifference function)
      (holderDividedDifference_continuous continuous) holder (holderDividedDifference_bound holder_bound)), by
    constructor
    · intro pair
      change (Real.sqrt |pair.val.1 - pair.val.2| : ℂ) *
        ((function pair.val.1 - function pair.val.2) / (Real.sqrt |pair.val.1 - pair.val.2| : ℂ)) = _
      have nonzero : (Real.sqrt |pair.val.1 - pair.val.2| : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr pair.property))).ne'
      field_simp
    · exact periodic⟩

theorem PeriodicHolderHalf.ofFunction_norm_bound (function : ℝ → ℂ) (continuous : Continuous function)
    {valueBound holder : ℝ} (value_nonneg : 0 ≤ valueBound) (holder_nonneg : 0 ≤ holder)
    (value_bound : ∀ label, ‖function label‖ ≤ valueBound)
    (holder_bound : ∀ first second : ℝ,
      ‖function first - function second‖ ≤ holder * Real.sqrt |first - second|)
    (periodic : Function.Periodic function (2 * Real.pi)) :
    ‖PeriodicHolderHalf.ofFunction function continuous valueBound holder value_bound holder_bound periodic‖ ≤
      max valueBound holder := by
  exact max_le_max
    (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le continuous value_nonneg value_bound)
    (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
      (holderDividedDifference_continuous continuous) holder_nonneg (holderDividedDifference_bound holder_bound))

def boundedIntervalIntegral (lower upper : ℝ) : (ℝ →ᵇ ℂ) →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun function => ∫ source in lower..upper, function source
      map_add' := fun first second => intervalIntegral.integral_add
        (first.continuous.intervalIntegrable lower upper) (second.continuous.intervalIntegrable lower upper)
      map_smul' := fun scalar function => intervalIntegral.integral_smul scalar function }
    |upper - lower| (fun function => by
      have estimate := intervalIntegral.norm_integral_le_of_norm_le_const
        (fun source _ => function.norm_coe_le_norm source)
        (a := lower) (b := upper)
      simpa only [mul_comm] using estimate)

abbrev C1HolderGraphAmbient := (ℝ →ᵇ ℂ) × PeriodicHolderHalf

def periodicC1HolderGraph : Submodule ℝ C1HolderGraphAmbient where
  carrier := {data | (∀ label : ℝ,
      data.1 label - data.1 0 = boundedIntervalIntegral 0 label data.2.val.1) ∧
    ∀ label : ℝ, data.1 (label + 2 * Real.pi) = data.1 label}
  zero_mem' := by simp [boundedIntervalIntegral]
  add_mem' := by
    intro first second first_mem second_mem
    constructor
    · intro label
      change (first.1 label + second.1 label) - (first.1 0 + second.1 0) =
        boundedIntervalIntegral 0 label (first.2.val.1 + second.2.val.1)
      rw [map_add, ← first_mem.1 label, ← second_mem.1 label]
      ring
    · intro label
      change first.1 _ + second.1 _ = first.1 _ + second.1 _
      rw [first_mem.2 label, second_mem.2 label]
  smul_mem' := by
    intro scalar data membership
    constructor
    · intro label
      change scalar • data.1 label - scalar • data.1 0 =
        boundedIntervalIntegral 0 label (scalar • data.2.val.1)
      rw [map_smul, ← membership.1 label, smul_sub]
    · intro label
      change scalar • data.1 _ = scalar • data.1 _
      rw [membership.2 label]

theorem periodicC1HolderGraph_isClosed : IsClosed (periodicC1HolderGraph : Set C1HolderGraphAmbient) := by
  change IsClosed {data : C1HolderGraphAmbient |
    (∀ label : ℝ, data.1 label - data.1 0 = boundedIntervalIntegral 0 label data.2.val.1) ∧
    ∀ label : ℝ, data.1 (label + 2 * Real.pi) = data.1 label}
  apply IsClosed.inter
  · have closed : ∀ label : ℝ, IsClosed {data : C1HolderGraphAmbient |
        data.1 label - data.1 0 = boundedIntervalIntegral 0 label data.2.val.1} := by
      intro label
      exact isClosed_eq
        (((BoundedContinuousFunction.continuous_eval_const).comp continuous_fst).sub
          ((BoundedContinuousFunction.continuous_eval_const).comp continuous_fst))
        ((boundedIntervalIntegral 0 label).continuous.comp
          ((continuous_fst.comp continuous_subtype_val).comp continuous_snd))
    convert isClosed_iInter closed using 1
    ext data
    simp
    rfl
  · have closed : ∀ label : ℝ, IsClosed {data : C1HolderGraphAmbient |
        data.1 (label + 2 * Real.pi) = data.1 label} := by
      intro label
      exact isClosed_eq
        ((BoundedContinuousFunction.continuous_eval_const).comp continuous_fst)
        ((BoundedContinuousFunction.continuous_eval_const).comp continuous_fst)
    convert isClosed_iInter closed using 1
    ext data
    simp
    rfl

abbrev PeriodicC1HolderHalf := periodicC1HolderGraph

instance : CompleteSpace PeriodicC1HolderHalf := periodicC1HolderGraph_isClosed.completeSpace_coe

theorem PeriodicC1HolderHalf.hasDerivAt (data : PeriodicC1HolderHalf) (label : ℝ) :
    HasDerivAt data.val.1 (data.val.2.val.1 label) label := by
  have identity : (fun current => data.val.1 0 + ∫ source in (0 : ℝ)..current, data.val.2.val.1 source) =
      data.val.1 := by
    funext current
    have actual := data.property.1 current
    change data.val.1 current - data.val.1 0 = ∫ source in (0 : ℝ)..current, data.val.2.val.1 source at actual
    rw [← actual]
    abel
  rw [← identity]
  exact (data.val.2.val.1.continuous.integral_hasStrictDerivAt 0 label).hasDerivAt.const_add _

theorem PeriodicC1HolderHalf.derivative_holder_bound (data : PeriodicC1HolderHalf) (first second : ℝ) :
    ‖data.val.2.val.1 first - data.val.2.val.1 second‖ ≤ ‖data‖ * Real.sqrt |first - second| := by
  exact (PeriodicHolderHalf.holder_bound data.val.2 first second).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))

end

end EulerNonuniqueness.Paper
