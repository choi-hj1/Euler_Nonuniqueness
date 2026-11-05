import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open Set MeasureTheory Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

theorem tendsto_integral_norm_indicator_sub_of_persistence
    (domain : ℝ → Set ℂ) (time : ℝ)
    (measurable : ∀ parameter, MeasurableSet (domain parameter))
    (finite : ∀ parameter, volume (domain parameter) ≠ ⊤)
    (persistence : ∀ position ∈ domain time, ∀ᶠ parameter in 𝓝 time, position ∈ domain parameter)
    (area_constant : ∀ᶠ parameter in 𝓝 time,
      (volume (domain parameter)).toReal = (volume (domain time)).toReal) :
    Tendsto (fun parameter => ∫ position,
      ‖(domain parameter).indicator (fun _ => (1 : ℝ)) position -
        (domain time).indicator (fun _ => (1 : ℝ)) position‖) (𝓝 time) (𝓝 0) := by
  let indicator : ℝ → ℂ → ℝ := fun parameter => (domain parameter).indicator (fun _ => (1 : ℝ))
  let intersection : ℝ → ℂ → ℝ := fun parameter position => indicator parameter position * indicator time position
  have indicator_integrable (parameter : ℝ) : Integrable (indicator parameter) :=
    memLp_one_iff_integrable.mp (memLp_indicator_const 1 (measurable parameter) 1 (Or.inr (finite parameter)))
  have indicator_integral (parameter : ℝ) : (∫ position, indicator parameter position) = (volume (domain parameter)).toReal := by
    dsimp only [indicator]
    rw [integral_indicator (measurable parameter), setIntegral_const]
    simp only [smul_eq_mul, mul_one]
    rfl
  have intersection_bound (parameter : ℝ) (position : ℂ) : ‖intersection parameter position‖ ≤ indicator time position := by
    dsimp only [intersection, indicator]
    by_cases first : position ∈ domain parameter <;> by_cases second : position ∈ domain time <;>
      simp [first, second]
  have intersection_measurable (parameter : ℝ) : AEStronglyMeasurable (intersection parameter) :=
    ((indicator_integrable parameter).aestronglyMeasurable.mul (indicator_integrable time).aestronglyMeasurable)
  have intersection_integrable (parameter : ℝ) : Integrable (intersection parameter) :=
    (indicator_integrable time).mono' (intersection_measurable parameter)
      (Eventually.of_forall (intersection_bound parameter))
  have intersection_convergence : Tendsto (fun parameter => ∫ position, intersection parameter position)
      (𝓝 time) (𝓝 ((volume (domain time)).toReal)) := by
    rw [← indicator_integral time]
    apply tendsto_integral_filter_of_dominated_convergence (indicator time)
    · exact Eventually.of_forall intersection_measurable
    · exact Eventually.of_forall fun parameter => Eventually.of_forall (intersection_bound parameter)
    · exact indicator_integrable time
    · exact Eventually.of_forall fun position => by
        by_cases inside : position ∈ domain time
        · apply tendsto_const_nhds.congr'
          filter_upwards [persistence position inside] with parameter membership
          simp [intersection, indicator, inside, membership]
        · have identity : (fun parameter => intersection parameter position) = fun _ => indicator time position := by
            funext parameter
            simp [intersection, indicator, inside]
          rw [identity]
          exact tendsto_const_nhds
  have norm_integral_identity (parameter : ℝ) :
      (∫ position, ‖indicator parameter position - indicator time position‖) =
      (volume (domain parameter)).toReal + (volume (domain time)).toReal -
        2 * ∫ position, intersection parameter position := by
    have integrand_identity : (fun position => ‖indicator parameter position - indicator time position‖) =
        (fun position => indicator parameter position + indicator time position - 2 * intersection parameter position) := by
      funext position
      dsimp only [intersection, indicator]
      by_cases first : position ∈ domain parameter <;> by_cases second : position ∈ domain time <;>
        norm_num [first, second]
    have added_integrable : Integrable (fun position => indicator parameter position + indicator time position) :=
      (indicator_integrable parameter).add (indicator_integrable time)
    rw [integrand_identity, integral_sub added_integrable
      ((intersection_integrable parameter).const_mul 2),
      integral_add (indicator_integrable parameter) (indicator_integrable time), integral_const_mul,
      indicator_integral parameter, indicator_integral time]
  have constant_comparison :
      (fun parameter => ∫ position, ‖indicator parameter position - indicator time position‖) =ᶠ[𝓝 time]
      (fun parameter => (volume (domain time)).toReal + (volume (domain time)).toReal -
        2 * ∫ position, intersection parameter position) := by
    filter_upwards [area_constant] with parameter equality
    rw [norm_integral_identity, equality]
  have convergence : Tendsto (fun parameter =>
      (volume (domain time)).toReal + (volume (domain time)).toReal -
        2 * ∫ position, intersection parameter position) (𝓝 time)
      (𝓝 ((volume (domain time)).toReal + (volume (domain time)).toReal -
        2 * (volume (domain time)).toReal)) :=
    (tendsto_const_nhds.add tendsto_const_nhds).sub (intersection_convergence.const_mul 2)
  have limit_identity : (volume (domain time)).toReal + (volume (domain time)).toReal -
      2 * (volume (domain time)).toReal = 0 := by ring
  rw [limit_identity] at convergence
  exact convergence.congr' constant_comparison.symm

end

end EulerNonuniqueness.Paper
