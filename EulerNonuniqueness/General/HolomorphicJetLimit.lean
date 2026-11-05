import Mathlib.Analysis.Complex.LocallyUniformLimit

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]
  [CompleteSpace Target]

theorem differentiableOn_of_uniform_linear_error
    (approximants : ℂ → ℂ → Target) (function : ℂ → Target) (domain : Set ℂ)
    (openDomain : IsOpen domain) {constant : ℝ}
    (error : ∀ᶠ parameter in 𝓝[≠] (0 : ℂ), ∀ point ∈ domain,
      ‖approximants parameter point - function point‖ ≤ constant * ‖parameter‖)
    (holomorphic : ∀ᶠ parameter in 𝓝[≠] (0 : ℂ),
      DifferentiableOn ℂ (approximants parameter) domain) :
    DifferentiableOn ℂ function domain := by
  have vanishes : Tendsto (fun parameter : ℂ => constant * ‖parameter‖)
      (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have continuous : Continuous (fun parameter : ℂ => constant * ‖parameter‖) :=
      continuous_const.mul continuous_norm
    simpa using (continuous.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  have uniform : TendstoUniformlyOn approximants function (𝓝[≠] (0 : ℂ)) domain := by
    refine Metric.tendstoUniformlyOn_iff.mpr fun tolerance positive => ?_
    filter_upwards [error, (tendsto_order.1 vanishes).2 tolerance positive] with parameter bound small
    intro point inside
    rw [dist_comm, dist_eq_norm]
    exact (bound point inside).trans_lt small
  exact uniform.tendstoLocallyUniformlyOn.differentiableOn holomorphic openDomain

end EulerNonuniqueness.General
