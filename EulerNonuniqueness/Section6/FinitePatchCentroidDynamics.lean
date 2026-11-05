import EulerNonuniqueness.Section6.FinitePatchCentroidComparison
import EulerNonuniqueness.Section6.FinitePointDynamics

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

def componentVorticity (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) (index : Fin count) : Vorticity :=
  (flow.domain time index).indicator (fun _ => configuration.density index)

theorem componentVorticity_memLp (flow : FiniteLiteralPatchFlow configuration)
    (time : ℝ) (index : Fin count) (exponent : ℝ≥0∞) :
    MemLp (flow.componentVorticity time index) exponent volume := by
  exact memLp_indicator_const exponent (flow.domain_isOpen time index).measurableSet _
    (Or.inr (flow.domain_isBounded time index).measure_lt_top.ne)

theorem componentVorticity_integrable (flow : FiniteLiteralPatchFlow configuration)
    (time : ℝ) (index : Fin count) : Integrable (flow.componentVorticity time index) :=
  memLp_one_iff_integrable.mp (flow.componentVorticity_memLp time index 1)

theorem vorticity_eq_sum_components (flow : FiniteLiteralPatchFlow configuration)
    (time : ℝ) (position : ℂ) :
    flow.vorticity time position = ∑ index, flow.componentVorticity time index position := by
  unfold vorticity FiniteContourConfiguration.literalVorticity
  apply Finset.sum_congr rfl
  intro index _
  change configuration.density index * (flow.domain time index).indicator (fun _ => (1 : ℝ)) position =
    (flow.domain time index).indicator (fun _ => configuration.density index) position
  by_cases member : position ∈ flow.domain time index <;> simp [member]

theorem biotSavart_eq_sum_components (flow : FiniteLiteralPatchFlow configuration)
    (time : ℝ) (position : ℂ) :
    biotSavart (flow.vorticity time) position =
      ∑ index, biotSavart (flow.componentVorticity time index) position := by
  have identity : (fun source => flow.vorticity time source • biotSavartKernel (position - source)) =
      fun source => ∑ index, flow.componentVorticity time index source • biotSavartKernel (position - source) := by
    funext source
    rw [flow.vorticity_eq_sum_components, Finset.sum_smul]
  unfold biotSavart
  rw [identity]
  exact integral_finset_sum _ (fun index _ => integrable_biotSavart_integrand_of_L1_L4
    (flow.componentVorticity_integrable time index) (flow.componentVorticity_memLp time index _) position)

theorem componentVelocity_integrableOn_domain (flow : FiniteLiteralPatchFlow configuration)
    (time : ℝ) (receiver source : Fin count) :
    IntegrableOn (biotSavart (flow.componentVorticity time source)) (flow.domain time receiver) :=
  Section6.integrableOn_biotSavart_of_L1_L4_finite
    (flow.componentVorticity_integrable time source) (flow.componentVorticity_memLp time source _)
    (flow.domain_isBounded time receiver).measure_lt_top

theorem centroid_hasDerivAt_sum_integrals (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (receiver : Fin count) :
    HasDerivAt (fun parameter => flow.centroid parameter receiver)
      (∑ source, (Real.pi * configuration.radius receiver ^ 2)⁻¹ •
        (∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position)) time := by
  have identity :
      (Real.pi * configuration.radius receiver ^ 2)⁻¹ •
        (∫ position in flow.domain time receiver, biotSavart (flow.vorticity time) position) =
      ∑ source, (Real.pi * configuration.radius receiver ^ 2)⁻¹ •
        (∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position) := by
    simp_rw [flow.biotSavart_eq_sum_components]
    rw [integral_finset_sum _ (fun source _ => flow.componentVelocity_integrableOn_domain time receiver source),
      Finset.smul_sum]
  rw [← identity]
  exact flow.centroid_hasDerivAt_complex_integral inside receiver

theorem component_self_integral_zero (flow : FiniteLiteralPatchFlow configuration)
    (time : ℝ) (index : Fin count) :
    (∫ position in flow.domain time index, biotSavart (flow.componentVorticity time index) position) = 0 := by
  obtain ⟨radius, _, radiusBound⟩ := (flow.domain_isBounded time index).exists_pos_norm_le
  exact Section6.integral_patch_self_interaction_density (flow.domain_isOpen time index).measurableSet
    (show flow.domain time index ⊆ Metric.closedBall 0 radius from fun position member => by
      simpa using radiusBound position member) (configuration.density index)

theorem centroid_hasDerivAt_external_sum_integrals (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (receiver : Fin count) :
    HasDerivAt (fun parameter => flow.centroid parameter receiver)
      (∑ source ∈ Finset.univ.erase receiver, (Real.pi * configuration.radius receiver ^ 2)⁻¹ •
        (∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position)) time := by
  have identity := Finset.sum_erase_add Finset.univ
    (fun source => (Real.pi * configuration.radius receiver ^ 2)⁻¹ •
      (∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position))
    (Finset.mem_univ receiver)
  dsimp only at identity
  rw [flow.component_self_integral_zero time receiver, smul_zero, add_zero] at identity
  rw [identity]
  exact flow.centroid_hasDerivAt_sum_integrals inside receiver

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
