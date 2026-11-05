import EulerNonuniqueness.Section6.PatchQuadraticDeformation
import EulerNonuniqueness.Section6.PatchComplexSecondMoment

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 200000

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem integral_square_recenter (domain : Set ℂ) (center reference : ℂ)
    (finite : volume domain < ⊤)
    (centeredIntegrable : IntegrableOn (fun position : ℂ => position - center) domain)
    (squareIntegrable : IntegrableOn (fun position : ℂ => (position - center) ^ 2) domain)
    (centeredZero : (∫ position in domain, position - center) = 0) :
    (∫ position in domain, (position - reference) ^ 2) =
      volume.real domain • (center - reference) ^ 2 +
        (∫ position in domain, (position - center) ^ 2) := by
  have constantIntegrable : IntegrableOn (fun _ : ℂ => (center - reference) ^ 2) domain :=
    integrableOn_const.mpr (Or.inr finite)
  have mixedIntegrable : IntegrableOn
      (fun position : ℂ => (2 * (center - reference)) * (position - center)) domain :=
    centeredIntegrable.const_mul (2 * (center - reference))
  have expansion : (fun position : ℂ => (position - reference) ^ 2) =
      (fun position : ℂ => (position - center) ^ 2 +
        (2 * (center - reference)) * (position - center) + (center - reference) ^ 2) := by
    funext position
    ring
  have mixedZero : (∫ position in domain, (2 * (center - reference)) * (position - center)) = 0 := by
    rw [integral_const_mul, centeredZero, mul_zero]
  have constantIntegral : (∫ _ : ℂ in domain, (center - reference) ^ 2) =
      volume.real domain • (center - reference) ^ 2 := by
    simpa only [Measure.real, Measure.restrict_apply_univ] using
      integral_const (μ := volume.restrict domain) ((center - reference) ^ 2)
  calc
    _ = ∫ position in domain, (position - center) ^ 2 +
        (2 * (center - reference)) * (position - center) + (center - reference) ^ 2 :=
      congrArg (fun function : ℂ → ℂ => ∫ position in domain, function position) expansion
    _ = (∫ position in domain, (position - center) ^ 2 +
        (2 * (center - reference)) * (position - center)) +
        (∫ _ : ℂ in domain, (center - reference) ^ 2) :=
      integral_add (squareIntegrable.add mixedIntegrable) constantIntegrable
    _ = ((∫ position in domain, (position - center) ^ 2) +
        (∫ position in domain, (2 * (center - reference)) * (position - center))) +
        (∫ _ : ℂ in domain, (center - reference) ^ 2) :=
      congrArg (fun result : ℂ => result + (∫ _ : ℂ in domain, (center - reference) ^ 2))
        (integral_add squareIntegrable mixedIntegrable)
    _ = _ := by rw [mixedZero, constantIntegral, add_zero, add_comm]

theorem domain_complex_second_moment_centroid_identity (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) (reference : ℂ) :
    (∫ position in flow.domain time index, (position - reference) ^ 2) =
      (Real.pi * configuration.radius index ^ 2) • (flow.centroid time index - reference) ^ 2 +
        (∫ position in flow.domain time index, (position - flow.centroid time index) ^ 2) := by
  let center := flow.centroid time index
  have centeredIntegrable : IntegrableOn (fun position : ℂ => position - center)
      (flow.domain time index) :=
    (((continuous_id.sub continuous_const).continuousOn.integrableOn_compact
      (flow.domain_isBounded time index).isCompact_closure).mono_set subset_closure)
  have squareIntegrable : IntegrableOn (fun position : ℂ => (position - center) ^ 2)
      (flow.domain time index) :=
    ((((continuous_id.sub continuous_const).pow 2).continuousOn.integrableOn_compact
      (flow.domain_isBounded time index).isCompact_closure).mono_set subset_closure)
  have identity := integral_square_recenter (flow.domain time index) center reference
    (flow.domain_isBounded time index).measure_lt_top centeredIntegrable squareIntegrable
    (flow.domain_centroid_centered_integral inside index)
  have area : volume.real (flow.domain time index) = Real.pi * configuration.radius index ^ 2 :=
    flow.domain_area inside index
  rw [area] at identity
  exact identity

theorem domain_complex_second_moment_point_error (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) (reference : ℂ)
    (small : ‖flow.shape time index - standardCircleBanach‖ ≤ 1 / 16) :
    ‖(∫ position in flow.domain time index, (position - reference) ^ 2) -
        (Real.pi * configuration.radius index ^ 2) • (flow.centroid time index - reference) ^ 2‖ ≤
      128 * Real.pi * configuration.radius index ^ 4 *
        ‖flow.shape time index - standardCircleBanach‖ := by
  rw [flow.domain_complex_second_moment_centroid_identity inside index reference, add_sub_cancel_left]
  exact flow.domain_centered_complex_second_moment_deformation_bound inside index small

theorem subfamily_complex_second_moment_point_error (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration)
    (indices : Finset (Fin count)) (reference : ℂ)
    (small : ∀ index ∈ indices, ‖flow.shape time index - standardCircleBanach‖ ≤ 1 / 16) :
    ‖(∑ index ∈ indices, configuration.density index •
        (∫ position in flow.domain time index, (position - reference) ^ 2)) -
      ∑ index ∈ indices, (configuration.density index * (Real.pi * configuration.radius index ^ 2)) •
        (flow.centroid time index - reference) ^ 2‖ ≤
      ∑ index ∈ indices, 128 * |configuration.density index * (Real.pi * configuration.radius index ^ 2)| *
        configuration.radius index ^ 2 * ‖flow.shape time index - standardCircleBanach‖ := by
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro index member
  rw [mul_smul, ← smul_sub, norm_smul, Real.norm_eq_abs]
  have estimate := mul_le_mul_of_nonneg_left
    (flow.domain_complex_second_moment_point_error inside index reference (small index member))
    (abs_nonneg (configuration.density index))
  apply estimate.trans_eq
  rw [abs_mul, abs_of_nonneg (show 0 ≤ Real.pi * configuration.radius index ^ 2 by positivity)]
  ring

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
