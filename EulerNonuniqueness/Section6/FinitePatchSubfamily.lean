import EulerNonuniqueness.Section6.FinitePatchCentroidDynamics
import EulerNonuniqueness.Section3.FiniteLiteralPatchDomination
import EulerNonuniqueness.Section6.VorticityAngularCancellation

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

def subfamilyVorticity (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) (time : ℝ) : Vorticity :=
  fun position => ∑ index ∈ selected, flow.componentVorticity time index position

theorem subfamilyVorticity_univ (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) :
    flow.subfamilyVorticity Finset.univ time = flow.vorticity time := by
  funext position
  exact (flow.vorticity_eq_sum_components time position).symm

theorem subfamilyVorticity_memLp (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) (time : ℝ) (exponent : ℝ≥0∞) :
    MemLp (flow.subfamilyVorticity selected time) exponent volume := by
  exact memLp_finset_sum _ fun index _ => flow.componentVorticity_memLp time index exponent

theorem subfamilyVorticity_integrable (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) (time : ℝ) :
    Integrable (flow.subfamilyVorticity selected time) :=
  memLp_one_iff_integrable.mp (flow.subfamilyVorticity_memLp selected time 1)

theorem abs_subfamilyVorticity_le (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) (time : ℝ) (position : ℂ) :
    |flow.subfamilyVorticity selected time position| ≤ ∑ index ∈ selected, |configuration.density index| := by
  change ‖∑ index ∈ selected, flow.componentVorticity time index position‖ ≤ _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro index _
  by_cases member : position ∈ flow.domain time index
  · simp only [componentVorticity, indicator_of_mem member, Real.norm_eq_abs, le_refl]
  · simp only [componentVorticity, indicator_of_not_mem member, norm_zero]
    exact abs_nonneg _

theorem subfamilyVorticity_support (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) (time : ℝ) :
    Function.support (flow.subfamilyVorticity selected time) ⊆
      Metric.closedBall 0 (∑ index : Fin count, (‖configuration.center index‖ + 2 * configuration.radius index)) := by
  intro position nonzero
  by_contra outside
  have positionLarge : (∑ index : Fin count, (‖configuration.center index‖ + 2 * configuration.radius index)) < ‖position‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using outside
  have vanishing (index : Fin count) : flow.componentVorticity time index position = 0 := by
    apply indicator_of_not_mem
    intro member
    have localBound := flow.domain_subset_ball time index member
    rw [Metric.mem_ball, dist_eq_norm] at localBound
    have centerBound : ‖configuration.center index‖ + 2 * configuration.radius index ≤
        ∑ other : Fin count, (‖configuration.center other‖ + 2 * configuration.radius other) := by
      exact Finset.single_le_sum (fun other _ =>
        add_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) (configuration.radius_pos other).le)) (Finset.mem_univ index)
    have triangle := norm_add_le (position - configuration.center index) (configuration.center index)
    rw [sub_add_cancel] at triangle
    linarith
  exact nonzero (by simp only [subfamilyVorticity, vanishing, Finset.sum_const_zero])

theorem integral_subfamilyVorticity_smul {value : Type*}
    [NormedAddCommGroup value] [NormedSpace ℝ value]
    (flow : FiniteLiteralPatchFlow configuration) (selected : Finset (Fin count))
    (time : ℝ) (function : ℂ → value)
    (integrable : ∀ index ∈ selected, IntegrableOn function (flow.domain time index)) :
    (∫ position, flow.subfamilyVorticity selected time position • function position) =
      ∑ index ∈ selected, configuration.density index •
        ∫ position in flow.domain time index, function position := by
  have termIdentity (index : Fin count) :
      (fun position => flow.componentVorticity time index position • function position) =
      fun position => configuration.density index • (flow.domain time index).indicator function position := by
    funext position
    by_cases member : position ∈ flow.domain time index <;> simp [componentVorticity, member]
  have termIntegrable (index : Fin count) (inside : index ∈ selected) :
      Integrable (fun position => flow.componentVorticity time index position • function position) := by
    rw [termIdentity]
    exact ((integrable_indicator_iff (flow.domain_isOpen time index).measurableSet).mpr
      (integrable index inside)).smul _
  simp_rw [subfamilyVorticity, Finset.sum_smul]
  rw [integral_finset_sum _ termIntegrable]
  apply Finset.sum_congr rfl
  intro index _
  rw [termIdentity, integral_smul, integral_indicator (flow.domain_isOpen time index).measurableSet]

theorem integrable_subfamilyVorticity_smul {value : Type*}
    [NormedAddCommGroup value] [NormedSpace ℝ value]
    (flow : FiniteLiteralPatchFlow configuration) (selected : Finset (Fin count))
    (time : ℝ) (function : ℂ → value)
    (integrable : ∀ index ∈ selected, IntegrableOn function (flow.domain time index)) :
    Integrable (fun position => flow.subfamilyVorticity selected time position • function position) := by
  simp_rw [subfamilyVorticity, Finset.sum_smul]
  apply integrable_finset_sum
  intro index inside
  have termIdentity :
      (fun position => flow.componentVorticity time index position • function position) =
      fun position => configuration.density index • (flow.domain time index).indicator function position := by
    funext position
    by_cases member : position ∈ flow.domain time index <;> simp [componentVorticity, member]
  rw [termIdentity]
  exact ((integrable_indicator_iff (flow.domain_isOpen time index).measurableSet).mpr
    (integrable index inside)).smul _

theorem subfamily_internal_first_moment_zero (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) (time : ℝ) :
    (∫ position, flow.subfamilyVorticity selected time position •
      biotSavart (flow.subfamilyVorticity selected time) position) = 0 :=
  Section6.integral_vorticity_self_interaction
    (flow.subfamilyVorticity_integrable selected time) (flow.subfamilyVorticity_support selected time)
    (flow.abs_subfamilyVorticity_le selected time)

theorem subfamily_internal_angular_moment_zero (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) (time : ℝ) (center : ℂ) :
    (∫ position, @inner ℝ ℂ _ (position - center)
      (flow.subfamilyVorticity selected time position •
        biotSavart (flow.subfamilyVorticity selected time) position)) = 0 :=
  Section6.integral_vorticity_angular_self_interaction
    (flow.subfamilyVorticity_integrable selected time) (flow.subfamilyVorticity_support selected time)
    (flow.abs_subfamilyVorticity_le selected time) center

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
