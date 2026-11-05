import EulerNonuniqueness.Section6.FinitePatchRadialInertia
import EulerNonuniqueness.Section6.FinitePatchSubfamily

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem subfamily_radial_second_moment_point_error (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration)
    (selected : Finset (Fin count)) (center : ℂ) (referenceCenter : Fin count → ℂ)
    (error : Fin count → ℝ) (errorNonnegative : ∀ index ∈ selected, 0 ≤ error index)
    (errorSmall : ∀ index ∈ selected, error index ≤ 1 / 16)
    (lower : ∀ index ∈ selected,
      Metric.ball (referenceCenter index) (configuration.radius index * (1 - error index)) ⊆ flow.domain time index)
    (upper : ∀ index ∈ selected,
      flow.domain time index ⊆ Metric.ball (referenceCenter index) (configuration.radius index * (1 + error index))) :
    |(∫ position, flow.subfamilyVorticity selected time position * ‖position - center‖ ^ 2) -
        (∑ index ∈ selected, (configuration.density index * (Real.pi * configuration.radius index ^ 2)) *
          ‖flow.centroid time index - center‖ ^ 2) -
        ∑ index ∈ selected, configuration.density index * (Real.pi * configuration.radius index ^ 4 / 2)| ≤
      ∑ index ∈ selected, 76 * |configuration.density index * (Real.pi * configuration.radius index ^ 2)| *
        configuration.radius index ^ 2 * error index ^ 2 := by
  have integralIdentity := flow.integral_subfamilyVorticity_smul selected time
    (fun position : ℂ => ‖position - center‖ ^ 2) (fun index _ =>
      (((continuous_id.sub continuous_const).norm.pow 2).continuousOn.integrableOn_compact
        (flow.domain_isBounded time index).isCompact_closure).mono_set subset_closure)
  simp only [smul_eq_mul] at integralIdentity
  rw [integralIdentity, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have pointwise (index : Fin count) (_member : index ∈ selected) :
      configuration.density index * (∫ position in flow.domain time index, ‖position - center‖ ^ 2) -
          (configuration.density index * (Real.pi * configuration.radius index ^ 2)) *
            ‖flow.centroid time index - center‖ ^ 2 -
          configuration.density index * (Real.pi * configuration.radius index ^ 4 / 2) =
        configuration.density index *
          ((∫ position in flow.domain time index, ‖position - flow.centroid time index‖ ^ 2) -
            Real.pi * configuration.radius index ^ 4 / 2) := by
    rw [flow.domain_radial_moment_recenter inside index center]
    ring
  rw [Finset.sum_congr rfl pointwise]
  change ‖∑ index ∈ selected, configuration.density index *
      ((∫ position in flow.domain time index, ‖position - flow.centroid time index‖ ^ 2) -
        Real.pi * configuration.radius index ^ 4 / 2)‖ ≤ _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro index member
  exact flow.domain_weighted_radial_second_moment_bound_of_trapping inside index (referenceCenter index)
    (errorNonnegative index member) (errorSmall index member) (lower index member) (upper index member)

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
