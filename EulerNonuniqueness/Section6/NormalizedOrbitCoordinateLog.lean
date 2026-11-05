import EulerNonuniqueness.General.ExponentialProfileLog
import EulerNonuniqueness.Section6.NormalizedOrbitDepartureTarget

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Paper

theorem normalizedSeparatingOrbit_coordinate_log_time_tendsto
    {coordinate : ℝ → ℝ} (coordinateZero : coordinate 0 = 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit) :
    Tendsto (fun time => Real.log (coordinate (orbitUnstableShape orbit time)) /
      (2 * Real.sqrt 2) - time) atBot (𝓝 0) := by
  have unstableLimit := continuous_fst.continuousAt.tendsto.comp
    (normalizedSeparatingOrbit_shape_tendsto_zero orbit normalized)
  have positive := normalizedSeparatingOrbit_eventually_positive_unstable orbit normalized
  have rightLimit : Tendsto (orbitUnstableShape orbit) atBot (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨unstableLimit, positive⟩
  have slope : Tendsto (fun time => (orbitUnstableShape orbit time)⁻¹ *
      coordinate (orbitUnstableShape orbit time)) atBot (𝓝 1) := by
    simpa only [zero_add, coordinateZero, sub_zero, smul_eq_mul] using
      coordinateDerivative.tendsto_slope_zero_right.comp rightLimit
  have product := normalized.2.2.2.2.2.1.mul slope
  simp only [mul_one] at product
  have weighted : Tendsto (fun time => Real.exp (-(2 * Real.sqrt 2) * time) *
      coordinate (orbitUnstableShape orbit time)) atBot (𝓝 1) := by
    apply product.congr'
    filter_upwards [positive] with time nonzero
    field_simp [nonzero.ne']
    ring
  exact EulerNonuniqueness.General.tendsto_log_exp_profile_sub (by positivity : 2 * Real.sqrt (2 : ℝ) ≠ 0) weighted

end EulerNonuniqueness.Section6
