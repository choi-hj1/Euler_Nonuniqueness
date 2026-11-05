import EulerNonuniqueness.Section3.C1HolderOperations
import Mathlib.Analysis.NormedSpace.OperatorNorm.Bilinear
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance c1ContinuousOperationsContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance c1ContinuousOperationsUniformAddGroup : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)
local instance c1ContinuousOperationsOperatorTopology : TopologicalSpace (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.topologicalSpace (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
local instance c1ContinuousOperationsOperatorSeminormedGroup : SeminormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance c1ContinuousOperationsOperatorNormedSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

def c1ProductBilinear : PeriodicC1HolderHalf →ₗ[ℝ] PeriodicC1HolderHalf →ₗ[ℝ] PeriodicC1HolderHalf := {
  toFun := fun first => {
    toFun := c1Product first
    map_add' := fun second third => by
      apply PeriodicC1HolderHalf.ext_value
      intro label
      change first.val.1 label * (second.val.1 label + third.val.1 label) =
        first.val.1 label * second.val.1 label + first.val.1 label * third.val.1 label
      exact mul_add _ _ _
    map_smul' := fun scalar second => by
      apply PeriodicC1HolderHalf.ext_value
      intro label
      change first.val.1 label * (scalar • second.val.1 label) = scalar • (first.val.1 label * second.val.1 label)
      exact mul_smul_comm _ _ _ }
  map_add' := fun first second => by
    apply LinearMap.ext
    intro third
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (first.val.1 label + second.val.1 label) * third.val.1 label =
      first.val.1 label * third.val.1 label + second.val.1 label * third.val.1 label
    exact add_mul _ _ _
  map_smul' := fun scalar first => by
    apply LinearMap.ext
    intro second
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (scalar • first.val.1 label) * second.val.1 label = scalar • (first.val.1 label * second.val.1 label)
    exact smul_mul_assoc _ _ _ }

def c1ProductCLM : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  LinearMap.mkContinuous₂ (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
    (G := PeriodicC1HolderHalf) c1ProductBilinear 8 c1Product_norm_bound

set_option maxHeartbeats 1000000 in
theorem c1Product_continuous :
    Continuous (fun pair : PeriodicC1HolderHalf × PeriodicC1HolderHalf => c1Product pair.1 pair.2) := by
  apply continuous_iff_continuousAt.mpr
  intro pair
  apply tendsto_iff_dist_tendsto_zero.mpr
  let majorant := fun other : PeriodicC1HolderHalf × PeriodicC1HolderHalf =>
    8 * dist other.1 pair.1 * ‖other.2‖ + 8 * ‖pair.1‖ * dist other.2 pair.2
  have majorant_continuous : Continuous majorant := by
    exact ((continuous_const.mul (continuous_fst.dist continuous_const)).mul continuous_snd.norm).add
      (continuous_const.mul (continuous_snd.dist continuous_const))
  have majorant_limit : Filter.Tendsto majorant (nhds pair) (nhds 0) := by
    convert majorant_continuous.continuousAt.tendsto using 1
    simp only [majorant, dist_self, mul_zero, zero_mul, zero_add]
  apply squeeze_zero (fun _ => dist_nonneg) _ majorant_limit
  intro other
  dsimp only [majorant]
  rw [dist_eq_norm (c1Product other.1 other.2) (c1Product pair.1 pair.2),
    dist_eq_norm other.1 pair.1, dist_eq_norm other.2 pair.2]
  exact c1Product_difference_norm_bound _ _ _ _

def c1ConjugateCLM : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf := by
  let conjugate : PeriodicC1HolderHalf →ₗ[ℝ] PeriodicC1HolderHalf := {
    toFun := c1Conjugate
    map_add' := fun first second => by
      apply PeriodicC1HolderHalf.ext_value
      intro label
      change star (first.val.1 label + second.val.1 label) = star (first.val.1 label) + star (second.val.1 label)
      exact star_add _ _
    map_smul' := fun scalar data => by
      apply PeriodicC1HolderHalf.ext_value
      intro label
      change star (scalar • data.val.1 label) = scalar • star (data.val.1 label)
      simp only [star_smul, star_trivial] }
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
    conjugate 1 (fun data => by
      change ‖c1Conjugate data‖ ≤ 1 * ‖data‖
      simpa only [one_mul] using c1Conjugate_norm_bound data)

end

end EulerNonuniqueness.Paper
