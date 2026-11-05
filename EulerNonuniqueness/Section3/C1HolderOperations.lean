import EulerNonuniqueness.Section3.C1HolderInverse

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance c1OperationsHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance c1OperationsNormedSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

def c1Conjugate (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  PeriodicC1HolderHalf.ofFunctions (fun label => star (data.val.1 label))
    (holderConjugate data.val.2).val.1
    (continuous_star.comp data.val.1.continuous) (holderConjugate data.val.2).val.1.continuous
    ‖data‖ ‖holderConjugate data.val.2‖ ‖holderConjugate data.val.2‖
    (fun label => by rw [norm_star]; exact PeriodicC1HolderHalf.value_bound data label)
    (PeriodicHolderHalf.value_bound _) (PeriodicHolderHalf.holder_bound _)
    (fun label => (PeriodicC1HolderHalf.hasDerivAt data label).star)
    (fun label => by dsimp only; rw [PeriodicC1HolderHalf.periodic data label])
    (PeriodicHolderHalf.periodic _)

theorem c1Conjugate_value (data : PeriodicC1HolderHalf) (label : ℝ) :
    (c1Conjugate data).val.1 label = star (data.val.1 label) := rfl

theorem c1Conjugate_norm_bound (data : PeriodicC1HolderHalf) : ‖c1Conjugate data‖ ≤ ‖data‖ := by
  have tangent_eq : (c1Conjugate data).val.2 = holderConjugate data.val.2 := by
    apply PeriodicHolderHalf.ext_value
    intro label
    rfl
  change max ‖(c1Conjugate data).val.1‖ ‖(c1Conjugate data).val.2‖ ≤ _
  rw [tangent_eq]
  apply max_le
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg data)).mpr
    intro label
    rw [c1Conjugate_value, norm_star]
    exact PeriodicC1HolderHalf.value_bound data label
  · exact (holderConjugate_norm_bound data.val.2).trans (le_max_right _ _)

theorem c1Product_difference_identity (first second third fourth : PeriodicC1HolderHalf) :
    c1Product first second - c1Product third fourth =
      c1Product (first - third) second + c1Product third (second - fourth) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (c1Product first second).val.1 label - (c1Product third fourth).val.1 label =
    (c1Product (first - third) second).val.1 label + (c1Product third (second - fourth)).val.1 label
  simp only [c1Product_value]
  change first.val.1 label * second.val.1 label - third.val.1 label * fourth.val.1 label =
    (first.val.1 label - third.val.1 label) * second.val.1 label +
      third.val.1 label * (second.val.1 label - fourth.val.1 label)
  ring

theorem c1Product_difference_norm_bound (first second third fourth : PeriodicC1HolderHalf) :
    ‖c1Product first second - c1Product third fourth‖ ≤
      8 * ‖first - third‖ * ‖second‖ + 8 * ‖third‖ * ‖second - fourth‖ := by
  rw [c1Product_difference_identity]
  exact (norm_add_le _ _).trans (add_le_add (c1Product_norm_bound _ _) (c1Product_norm_bound _ _))

theorem c1Conjugate_difference_norm_bound (first second : PeriodicC1HolderHalf) :
    ‖c1Conjugate first - c1Conjugate second‖ ≤ ‖first - second‖ := by
  have identity : c1Conjugate first - c1Conjugate second = c1Conjugate (first - second) := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change star (first.val.1 label) - star (second.val.1 label) = star (first.val.1 label - second.val.1 label)
    exact (star_sub _ _).symm
  rw [identity]
  exact c1Conjugate_norm_bound _

def c1Constant (value : ℂ) : PeriodicC1HolderHalf :=
  PeriodicC1HolderHalf.ofFunctions (fun _ => value) (fun _ => 0)
    continuous_const continuous_const ‖value‖ 0 0
    (fun _ => le_rfl) (fun _ => by simp) (fun _ _ => by simp)
    (fun label => hasDerivAt_const label value) (fun _ => rfl) (fun _ => rfl)

theorem c1Constant_value (value : ℂ) (label : ℝ) :
    (c1Constant value).val.1 label = value := rfl

theorem c1Constant_norm_bound (value : ℂ) : ‖c1Constant value‖ ≤ ‖value‖ := by
  apply (PeriodicC1HolderHalf.ofFunctions_norm_bound _ _ _ _
    (norm_nonneg _) (le_refl 0) (le_refl 0) _ _ _ _ _ _).trans
  simp only [max_self, max_eq_left (norm_nonneg value)]
  exact le_rfl

def c1ConstantCLM : ℂ →L[ℝ] PeriodicC1HolderHalf := by
  let constant : ℂ →ₗ[ℝ] PeriodicC1HolderHalf := {
    toFun := c1Constant
    map_add' := fun first second => by
      apply PeriodicC1HolderHalf.ext_value
      intro label
      rfl
    map_smul' := fun scalar value => by
      apply PeriodicC1HolderHalf.ext_value
      intro label
      rfl }
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := ℂ) (F := PeriodicC1HolderHalf)
    constant 1 (fun value => by
      change ‖c1Constant value‖ ≤ 1 * ‖value‖
      simpa only [one_mul] using c1Constant_norm_bound value)

end

end EulerNonuniqueness.Paper
