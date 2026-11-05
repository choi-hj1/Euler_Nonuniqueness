import EulerNonuniqueness.Section3.ContourFlowStability

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance c1AlgebraHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance c1AlgebraNormedSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem PeriodicC1HolderHalf.value_holder_bound (data : PeriodicC1HolderHalf) (first second : ℝ) :
    ‖data.val.1 first - data.val.1 second‖ ≤ 2 * ‖data‖ * Real.sqrt |first - second| := by
  by_cases small : |first - second| ≤ 1
  · have distance_le_root : |first - second| ≤ Real.sqrt |first - second| := by
      have root_sq := Real.sq_sqrt (abs_nonneg (first - second))
      have root_nonneg := Real.sqrt_nonneg |first - second|
      nlinarith
    exact (PeriodicC1HolderHalf.lipschitz_bound data first second).trans
      ((mul_le_mul_of_nonneg_left distance_le_root (norm_nonneg data)).trans
        (by nlinarith [mul_nonneg (norm_nonneg data) (Real.sqrt_nonneg |first - second|)]))
  · have root_large : 1 ≤ Real.sqrt |first - second| := by
      have root_sq := Real.sq_sqrt (abs_nonneg (first - second))
      have root_nonneg := Real.sqrt_nonneg |first - second|
      push_neg at small
      nlinarith
    calc
      _ ≤ ‖data.val.1 first‖ + ‖data.val.1 second‖ := norm_sub_le _ _
      _ ≤ 2 * ‖data‖ := by linarith [PeriodicC1HolderHalf.value_bound data first, PeriodicC1HolderHalf.value_bound data second]
      _ ≤ _ := le_mul_of_one_le_right (by positivity) root_large

def c1ValueHolder (data : PeriodicC1HolderHalf) : PeriodicHolderHalf :=
  PeriodicHolderHalf.ofFunction data.val.1 data.val.1.continuous ‖data‖ (2 * ‖data‖)
    (PeriodicC1HolderHalf.value_bound data) (PeriodicC1HolderHalf.value_holder_bound data)
    (PeriodicC1HolderHalf.periodic data)

theorem c1ValueHolder_value (data : PeriodicC1HolderHalf) (label : ℝ) :
    (c1ValueHolder data).val.1 label = data.val.1 label := rfl

theorem c1ValueHolder_norm_bound (data : PeriodicC1HolderHalf) :
    ‖c1ValueHolder data‖ ≤ 2 * ‖data‖ := by
  apply PeriodicHolderHalf.norm_le_of_bounds _ (by positivity)
  · intro label
    rw [c1ValueHolder_value]
    exact (PeriodicC1HolderHalf.value_bound data label).trans (by nlinarith [norm_nonneg data])
  · intro first second
    exact PeriodicC1HolderHalf.value_holder_bound data first second

def c1ProductTangent (first second : PeriodicC1HolderHalf) : PeriodicHolderHalf :=
  holderProduct first.val.2 (c1ValueHolder second) + holderProduct (c1ValueHolder first) second.val.2

theorem c1ProductTangent_value (first second : PeriodicC1HolderHalf) (label : ℝ) :
    (c1ProductTangent first second).val.1 label =
      first.val.2.val.1 label * second.val.1 label + first.val.1 label * second.val.2.val.1 label := rfl

theorem c1ProductTangent_norm_bound (first second : PeriodicC1HolderHalf) :
    ‖c1ProductTangent first second‖ ≤ 8 * ‖first‖ * ‖second‖ := by
  have first_tangent : ‖first.val.2‖ ≤ ‖first‖ := le_max_right _ _
  have second_tangent : ‖second.val.2‖ ≤ ‖second‖ := le_max_right _ _
  calc
    _ ≤ ‖holderProduct first.val.2 (c1ValueHolder second)‖ +
        ‖holderProduct (c1ValueHolder first) second.val.2‖ := norm_add_le _ _
    _ ≤ 2 * ‖first.val.2‖ * ‖c1ValueHolder second‖ +
        2 * ‖c1ValueHolder first‖ * ‖second.val.2‖ :=
      add_le_add (holderProduct_norm_bound _ _) (holderProduct_norm_bound _ _)
    _ ≤ _ := by
      have left := mul_le_mul first_tangent (c1ValueHolder_norm_bound second) (norm_nonneg _) (norm_nonneg _)
      have right := mul_le_mul (c1ValueHolder_norm_bound first) second_tangent (norm_nonneg _) (by positivity)
      nlinarith

def c1Product (first second : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  PeriodicC1HolderHalf.ofFunctions
    (fun label => first.val.1 label * second.val.1 label)
    (c1ProductTangent first second).val.1
    (first.val.1.continuous.mul second.val.1.continuous)
    (c1ProductTangent first second).val.1.continuous
    (‖first‖ * ‖second‖) ‖c1ProductTangent first second‖ ‖c1ProductTangent first second‖
    (fun label => by
      rw [norm_mul]
      exact mul_le_mul (PeriodicC1HolderHalf.value_bound first label) (PeriodicC1HolderHalf.value_bound second label)
        (norm_nonneg _) (norm_nonneg _))
    (PeriodicHolderHalf.value_bound _) (PeriodicHolderHalf.holder_bound _)
    (fun label => (PeriodicC1HolderHalf.hasDerivAt first label).mul (PeriodicC1HolderHalf.hasDerivAt second label))
    ((PeriodicC1HolderHalf.periodic first).mul (PeriodicC1HolderHalf.periodic second)) (PeriodicHolderHalf.periodic _)

theorem c1Product_value (first second : PeriodicC1HolderHalf) (label : ℝ) :
    (c1Product first second).val.1 label = first.val.1 label * second.val.1 label := rfl

theorem c1Product_norm_bound (first second : PeriodicC1HolderHalf) :
    ‖c1Product first second‖ ≤ 8 * ‖first‖ * ‖second‖ := by
  apply (PeriodicC1HolderHalf.ofFunctions_norm_bound _ _ _ _
    (by positivity) (norm_nonneg _) (norm_nonneg _) _ _ _ _ _ _).trans
  apply max_le
  · nlinarith [mul_nonneg (norm_nonneg first) (norm_nonneg second)]
  · exact max_le (c1ProductTangent_norm_bound first second) (c1ProductTangent_norm_bound first second)

end

end EulerNonuniqueness.Paper
