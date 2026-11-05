import EulerNonuniqueness.Section3.HolderBanachModel
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance holderLabelCompositionRealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

structure PeriodicC1LabelMap where
  map : ℝ → ℝ
  slope : ℝ → ℝ
  bound : ℝ
  holder : ℝ
  bound_nonnegative : 0 ≤ bound
  holder_nonnegative : 0 ≤ holder
  continuous : Continuous map
  slope_continuous : Continuous slope
  hasDerivAt : ∀ label, HasDerivAt map (slope label) label
  add_period : ∀ label, map (label + 2 * Real.pi) = map label + 2 * Real.pi
  slope_periodic : Function.Periodic slope (2 * Real.pi)
  slope_bound : ∀ label, |slope label| ≤ bound
  lipschitz_bound : ∀ first second, |map first - map second| ≤ bound * |first - second|
  holder_bound : ∀ first second, |slope first - slope second| ≤ holder * Real.sqrt |first - second|

namespace PeriodicC1LabelMap

def operatorBound (labels : PeriodicC1LabelMap) : ℝ :=
  1 + labels.bound + labels.bound * Real.sqrt labels.bound + labels.holder

theorem operatorBound_nonnegative (labels : PeriodicC1LabelMap) : 0 ≤ labels.operatorBound := by
  dsimp only [operatorBound]
  exact add_nonneg (add_nonneg (add_nonneg (by norm_num) labels.bound_nonnegative)
    (mul_nonneg labels.bound_nonnegative (Real.sqrt_nonneg _))) labels.holder_nonnegative

theorem composed_tangent_bound (labels : PeriodicC1LabelMap) (data : PeriodicC1HolderHalf) (label : ℝ) :
    ‖(labels.slope label : ℂ) * data.val.2.val.1 (labels.map label)‖ ≤ labels.bound * ‖data‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (labels.slope_bound label) (PeriodicC1HolderHalf.speed_bound data _)
    (norm_nonneg _) labels.bound_nonnegative

theorem composed_tangent_holder_bound (labels : PeriodicC1LabelMap) (data : PeriodicC1HolderHalf) (first second : ℝ) :
    ‖(labels.slope first : ℂ) * data.val.2.val.1 (labels.map first) -
      (labels.slope second : ℂ) * data.val.2.val.1 (labels.map second)‖ ≤
      ((labels.bound * Real.sqrt labels.bound + labels.holder) * ‖data‖) * Real.sqrt |first - second| := by
  have root_bound : Real.sqrt |labels.map first - labels.map second| ≤
      Real.sqrt labels.bound * Real.sqrt |first - second| := by
    exact (Real.sqrt_le_sqrt (labels.lipschitz_bound first second)).trans_eq
      (Real.sqrt_mul labels.bound_nonnegative _)
  have first_bound : ‖data.val.2.val.1 (labels.map first) - data.val.2.val.1 (labels.map second)‖ ≤
      ‖data‖ * (Real.sqrt labels.bound * Real.sqrt |first - second|) :=
    (PeriodicC1HolderHalf.derivative_holder_bound data _ _).trans
      (mul_le_mul_of_nonneg_left root_bound (norm_nonneg data))
  have difference :
      (labels.slope first : ℂ) * data.val.2.val.1 (labels.map first) -
        (labels.slope second : ℂ) * data.val.2.val.1 (labels.map second) =
      (labels.slope first : ℂ) * (data.val.2.val.1 (labels.map first) - data.val.2.val.1 (labels.map second)) +
        ((labels.slope first : ℂ) - (labels.slope second : ℂ)) * data.val.2.val.1 (labels.map second) := by ring
  rw [difference]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  have first_product := mul_le_mul (labels.slope_bound first) first_bound
    (norm_nonneg _) labels.bound_nonnegative
  have second_product := mul_le_mul (labels.holder_bound first second)
    (PeriodicC1HolderHalf.speed_bound data (labels.map second)) (norm_nonneg _)
    (mul_nonneg labels.holder_nonnegative (Real.sqrt_nonneg _))
  exact (add_le_add first_product second_product).trans_eq (by ring)

def compose (labels : PeriodicC1LabelMap) (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  PeriodicC1HolderHalf.ofFunctions
    (fun label => data.val.1 (labels.map label))
    (fun label => (labels.slope label : ℂ) * data.val.2.val.1 (labels.map label))
    (data.val.1.continuous.comp labels.continuous)
    ((Complex.continuous_ofReal.comp labels.slope_continuous).mul (data.val.2.val.1.continuous.comp labels.continuous))
    ‖data‖ (labels.bound * ‖data‖) ((labels.bound * Real.sqrt labels.bound + labels.holder) * ‖data‖)
    (fun label => PeriodicC1HolderHalf.value_bound data _)
    (labels.composed_tangent_bound data) (labels.composed_tangent_holder_bound data)
    (fun label => by
      simpa only [Function.comp_apply, Complex.real_smul] using
        (PeriodicC1HolderHalf.hasDerivAt data (labels.map label)).scomp label (labels.hasDerivAt label))
    (fun label => by
      dsimp only
      rw [labels.add_period, PeriodicC1HolderHalf.periodic data])
    (fun label => by
      dsimp only
      rw [labels.add_period, labels.slope_periodic, PeriodicHolderHalf.periodic data.val.2])

theorem compose_value (labels : PeriodicC1LabelMap) (data : PeriodicC1HolderHalf) (label : ℝ) :
    (labels.compose data).val.1 label = data.val.1 (labels.map label) := rfl

theorem compose_tangent (labels : PeriodicC1LabelMap) (data : PeriodicC1HolderHalf) (label : ℝ) :
    (labels.compose data).val.2.val.1 label =
      (labels.slope label : ℂ) * data.val.2.val.1 (labels.map label) := rfl

theorem compose_norm_bound (labels : PeriodicC1LabelMap) (data : PeriodicC1HolderHalf) :
    ‖labels.compose data‖ ≤ labels.operatorBound * ‖data‖ := by
  have bound : ‖labels.compose data‖ ≤
      max ‖data‖ (max (labels.bound * ‖data‖) ((labels.bound * Real.sqrt labels.bound + labels.holder) * ‖data‖)) := by
    unfold compose
    exact PeriodicC1HolderHalf.ofFunctions_norm_bound _ _ _ _ (norm_nonneg data)
      (mul_nonneg labels.bound_nonnegative (norm_nonneg data))
      (mul_nonneg (add_nonneg (mul_nonneg labels.bound_nonnegative (Real.sqrt_nonneg _)) labels.holder_nonnegative) (norm_nonneg data))
      _ _ _ _ _ _
  apply bound.trans
  dsimp only [operatorBound]
  have product_nonnegative := mul_nonneg labels.bound_nonnegative (Real.sqrt_nonneg labels.bound)
  apply max_le
  · nlinarith [norm_nonneg data, labels.bound_nonnegative, labels.holder_nonnegative]
  · apply max_le <;> nlinarith [norm_nonneg data, labels.bound_nonnegative, labels.holder_nonnegative]

def composeCLM (labels : PeriodicC1LabelMap) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  LinearMap.mkContinuous
    { toFun := labels.compose
      map_add' := fun first second => by
        apply PeriodicC1HolderHalf.ext_value
        intro label
        rfl
      map_smul' := fun scalar data => by
        apply PeriodicC1HolderHalf.ext_value
        intro label
        rfl }
    labels.operatorBound (labels.compose_norm_bound)

theorem composeCLM_value (labels : PeriodicC1LabelMap) (data : PeriodicC1HolderHalf) (label : ℝ) :
    (labels.composeCLM data).val.1 label = data.val.1 (labels.map label) := rfl

end PeriodicC1LabelMap

end EulerNonuniqueness.Paper
