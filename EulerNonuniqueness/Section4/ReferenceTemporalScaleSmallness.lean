import EulerNonuniqueness.Section1.UniformPolynomialLengthSmallness
import EulerNonuniqueness.Section1.UniformTransportScaleSmallness

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_reference_temporal_scales_small (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ,
      ({scales with frequency := frequency}).omega index * ({scales with frequency := frequency}).length index ≤
          scales.location index ∧
        ({scales with frequency := frequency}).omega index ^ 4 *
          ({scales with frequency := frequency}).length index ≤ 1 := by
  filter_upwards [scales.eventually_omega_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    scales.eventually_omega_pow_length_lt (by linarith : 1 < scales.ratio) alphaPositive 4 (by norm_num : (0 : ℝ) < 1)]
    with frequency transport polynomial
  intro index
  exact ⟨by simpa only [one_mul] using (transport index).le, (polynomial index).le⟩

end EulerNonuniqueness.Paper
