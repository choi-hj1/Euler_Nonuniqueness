import EulerNonuniqueness.Section3.FiniteMovingPatchFamily
import EulerNonuniqueness.Section6.VorticityAngularCancellation

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

def subfamilyVorticity (flow : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) (time : ℝ) : Vorticity :=
  fun position => ∑ index ∈ selected, flow.patchVorticity time index position

theorem subfamilyVorticity_univ (flow : FiniteMovingPatchFamily count) (time : ℝ) :
    flow.subfamilyVorticity Finset.univ time = flow.vorticity time := by
  funext position
  rfl

theorem subfamilyVorticity_memLp (flow : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) (time : ℝ) (exponent : ℝ≥0∞) :
    MemLp (flow.subfamilyVorticity selected time) exponent volume := by
  exact memLp_finset_sum _ fun index _ => flow.patchVorticity_memLp time index exponent

theorem subfamilyVorticity_integrable (flow : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) (time : ℝ) :
    Integrable (flow.subfamilyVorticity selected time) :=
  memLp_one_iff_integrable.mp (flow.subfamilyVorticity_memLp selected time 1)

theorem abs_subfamilyVorticity_le (flow : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) (time : ℝ) (position : ℂ) :
    |flow.subfamilyVorticity selected time position| ≤ ∑ index ∈ selected, |flow.density index| := by
  change ‖∑ index ∈ selected, flow.patchVorticity time index position‖ ≤ _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro index _
  by_cases member : position ∈ (flow.patch index).domain time
  · simp only [patchVorticity, indicator_of_mem member, Real.norm_eq_abs, le_refl]
  · simp only [patchVorticity, indicator_of_not_mem member, norm_zero]
    exact abs_nonneg _

theorem subfamilyVorticity_support (flow : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) (time : ℝ) :
    Function.support (flow.subfamilyVorticity selected time) ⊆
      Metric.closedBall 0 (∑ index : Fin count, (‖(flow.patch index).center time‖ + 2 * (flow.patch index).radius)) := by
  intro position nonzero
  by_contra outside
  have positionLarge : (∑ index : Fin count, (‖(flow.patch index).center time‖ + 2 * (flow.patch index).radius)) < ‖position‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using outside
  have vanishing (index : Fin count) : flow.patchVorticity time index position = 0 := by
    apply indicator_of_not_mem
    intro member
    have localBound := (flow.patch index).domain_subset_ball time member
    rw [Metric.mem_ball, dist_eq_norm] at localBound
    have centerBound : ‖(flow.patch index).center time‖ + 2 * (flow.patch index).radius ≤
        ∑ other : Fin count, (‖(flow.patch other).center time‖ + 2 * (flow.patch other).radius) := by
      exact Finset.single_le_sum
        (f := fun other : Fin count => ‖(flow.patch other).center time‖ + 2 * (flow.patch other).radius)
        (fun other _ => add_nonneg (norm_nonneg ((flow.patch other).center time))
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (flow.patch other).radius_positive.le)) (Finset.mem_univ index)
    have triangle := norm_add_le (position - (flow.patch index).center time) ((flow.patch index).center time)
    rw [sub_add_cancel] at triangle
    linarith
  exact nonzero (by simp only [subfamilyVorticity, vanishing, Finset.sum_const_zero])

theorem integral_subfamilyVorticity_smul {value : Type*}
    [NormedAddCommGroup value] [NormedSpace ℝ value]
    (flow : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (time : ℝ) (function : ℂ → value)
    (integrable : ∀ index ∈ selected, IntegrableOn function ((flow.patch index).domain time)) :
    (∫ position, flow.subfamilyVorticity selected time position • function position) =
      ∑ index ∈ selected, flow.density index •
        ∫ position in (flow.patch index).domain time, function position := by
  have termIdentity (index : Fin count) :
      (fun position => flow.patchVorticity time index position • function position) =
      fun position => flow.density index • ((flow.patch index).domain time).indicator function position := by
    funext position
    by_cases member : position ∈ (flow.patch index).domain time <;> simp [patchVorticity, member]
  have termIntegrable (index : Fin count) (inside : index ∈ selected) :
      Integrable (fun position => flow.patchVorticity time index position • function position) := by
    rw [termIdentity]
    exact ((integrable_indicator_iff ((flow.patch index).domain_isOpen time).measurableSet).mpr
      (integrable index inside)).smul _
  simp_rw [subfamilyVorticity, Finset.sum_smul]
  rw [integral_finset_sum _ termIntegrable]
  apply Finset.sum_congr rfl
  intro index _
  rw [termIdentity, integral_smul, integral_indicator ((flow.patch index).domain_isOpen time).measurableSet]

theorem integrable_subfamilyVorticity_smul {value : Type*}
    [NormedAddCommGroup value] [NormedSpace ℝ value]
    (flow : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (time : ℝ) (function : ℂ → value)
    (integrable : ∀ index ∈ selected, IntegrableOn function ((flow.patch index).domain time)) :
    Integrable (fun position => flow.subfamilyVorticity selected time position • function position) := by
  simp_rw [subfamilyVorticity, Finset.sum_smul]
  apply integrable_finset_sum
  intro index inside
  have termIdentity :
      (fun position => flow.patchVorticity time index position • function position) =
      fun position => flow.density index • ((flow.patch index).domain time).indicator function position := by
    funext position
    by_cases member : position ∈ (flow.patch index).domain time <;> simp [patchVorticity, member]
  rw [termIdentity]
  exact ((integrable_indicator_iff ((flow.patch index).domain_isOpen time).measurableSet).mpr
    (integrable index inside)).smul _

theorem subfamily_internal_first_moment_zero (flow : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) (time : ℝ) :
    (∫ position, flow.subfamilyVorticity selected time position •
      biotSavart (flow.subfamilyVorticity selected time) position) = 0 :=
  Section6.integral_vorticity_self_interaction
    (flow.subfamilyVorticity_integrable selected time) (flow.subfamilyVorticity_support selected time)
    (flow.abs_subfamilyVorticity_le selected time)

theorem subfamily_internal_angular_moment_zero (flow : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) (time : ℝ) (center : ℂ) :
    (∫ position, @inner ℝ ℂ _ (position - center)
      (flow.subfamilyVorticity selected time position •
        biotSavart (flow.subfamilyVorticity selected time) position)) = 0 :=
  Section6.integral_vorticity_angular_self_interaction
    (flow.subfamilyVorticity_integrable selected time) (flow.subfamilyVorticity_support selected time)
    (flow.abs_subfamilyVorticity_le selected time) center

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
