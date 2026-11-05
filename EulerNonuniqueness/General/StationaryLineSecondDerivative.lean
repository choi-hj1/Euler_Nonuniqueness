import EulerNonuniqueness.General.SecondJetUniqueness

namespace EulerNonuniqueness.General

noncomputable section

open Filter
open scoped Topology

variable {Space Target : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem second_frechet_diagonal_zero_of_stationary_line
    (function : Space → Target) (base direction : Space)
    (second : Space →L[ℝ] Space →L[ℝ] Target)
    (first : ∀ᶠ point in 𝓝 base, DifferentiableAt ℝ function point)
    (secondDerivative : HasFDerivAt (fderiv ℝ function) second base)
    (kernel : fderiv ℝ function base direction = 0)
    (stationary : ∀ᶠ time in 𝓝 (0 : ℝ), function (base + time • direction) = function base) :
    second direction direction = 0 := by
  have peano := (second_frechet_line_peano function base direction second first secondDerivative).tendsto_inv_smul_nhds_zero
    |>.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  have constant : Tendsto (fun _ : ℝ => -((1 / 2 : ℝ) • second direction direction))
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : Target)) := by
    apply peano.congr'
    filter_upwards [stationary.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with time identity outside
    have nonzero : time ≠ 0 := by simpa using outside
    have half : (time ^ 2)⁻¹ * (time ^ 2 / 2) = (1 / 2 : ℝ) := by field_simp
    simp only [identity, kernel, sub_self, smul_zero, sub_zero, zero_sub, smul_neg, smul_smul, half]
  have zero : -((1 / 2 : ℝ) • second direction direction) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds constant
  exact (smul_eq_zero.mp (neg_eq_zero.mp zero)).resolve_left (by norm_num)

end

end EulerNonuniqueness.General
