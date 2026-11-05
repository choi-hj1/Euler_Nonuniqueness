import EulerNonuniqueness.General.LinearExponentialTaylor

namespace EulerNonuniqueness.General

noncomputable section

open Filter
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem linearExponentialCurve_first_slope (operator : Space →L[ℝ] Space) (initial : Space) :
    Tendsto (fun time : ℝ => time⁻¹ • (linearExponentialCurve operator initial time - initial))
      (𝓝[≠] (0 : ℝ)) (𝓝 (operator initial)) := by
  simpa only [zero_add, linearExponentialCurve_zero] using
    (linearExponentialCurve_hasDerivAt operator initial 0).tendsto_slope_zero

theorem linearExponentialCurve_second_slope (operator : Space →L[ℝ] Space) (initial : Space) :
    Tendsto (fun time : ℝ => (time ^ 2)⁻¹ •
      (linearExponentialCurve operator initial time - initial - time • operator initial))
      (𝓝[≠] (0 : ℝ)) (𝓝 ((1 / 2 : ℝ) • operator (operator initial))) := by
  have error := (linearExponentialCurve_second_order_remainder operator initial).tendsto_inv_smul_nhds_zero
    |>.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  have shifted := error.add_const ((1 / 2 : ℝ) • operator (operator initial))
  simp only [zero_add] at shifted
  apply shifted.congr'
  filter_upwards [self_mem_nhdsWithin] with time outside
  have nonzero : time ≠ 0 := by simpa using outside
  have scale : (time ^ 2)⁻¹ * (time ^ 2 / 2) = (1 / 2 : ℝ) := by field_simp
  rw [smul_sub, smul_smul, scale]
  abel

end

end EulerNonuniqueness.General
