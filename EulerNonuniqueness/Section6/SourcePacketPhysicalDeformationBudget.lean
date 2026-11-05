import EulerNonuniqueness.Section6.SourcePacketDeformationArbitraryBudget

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem source_packet_physical_deformation_comparison {circulation radius deformation decay distance gap factor : ℝ}
    (circulationNonnegative : 0 ≤ circulation) (deformationNonnegative : 0 ≤ deformation)
    (decayPositive : 0 < decay) (distancePositive : 0 < distance) (factorPositive : 0 < factor)
    (gapLower : factor * distance ≤ gap) :
    (16384 * circulation * radius ^ 2 * deformation / (Real.pi * gap ^ 4) +
      3072 * circulation * radius ^ 2 * deformation / (Real.pi * distance ^ 4)) / decay ≤
      (16384 / factor ^ 4 + 3072) * circulation * radius ^ 2 * deformation /
        (Real.pi * distance ^ 4 * decay) := by
  have numeratorNonnegative : 0 ≤ 16384 * circulation * radius ^ 2 * deformation := by positivity
  have denominatorBound := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (mul_pos factorPositive distancePositive).le gapLower 4) Real.pi_pos.le
  have first := div_le_div_of_nonneg_left numeratorNonnegative
    (mul_pos Real.pi_pos (pow_pos (mul_pos factorPositive distancePositive) 4)) denominatorBound
  calc
    _ ≤ (16384 * circulation * radius ^ 2 * deformation / (Real.pi * (factor * distance) ^ 4) +
        3072 * circulation * radius ^ 2 * deformation / (Real.pi * distance ^ 4)) / decay :=
      div_le_div_of_nonneg_right (add_le_add_right first _) decayPositive.le
    _ = _ := by
      field_simp [factorPositive.ne', distancePositive.ne', decayPositive.ne', Real.pi_ne_zero]
      <;> ring

theorem Scales.eventually_source_packet_physical_deformation_budget (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    {scaleRoot boundaryConstant factor tolerance : ℝ} (rootPositive : 0 < scaleRoot)
    (boundaryNonnegative : 0 ≤ boundaryConstant) (factorPositive : 0 < factor)
    (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ, ∀ distance gap : ℝ, 0 < distance → factor * distance ≤ gap →
    let changed := {scales with frequency := frequency}
    let deformation := boundaryConstant / (scaleRoot ^ 2 * changed.omega (index + 1) ^ 2)
    (16384 * changed.circulation (index + 1) * changed.radius (index + 1) ^ 2 * deformation / (Real.pi * gap ^ 4) +
      3072 * changed.circulation (index + 1) * changed.radius (index + 1) ^ 2 * deformation / (Real.pi * distance ^ 4)) /
        (2 * Real.sqrt 2 * changed.omega index) ≤
      tolerance * (Real.sqrt 3 * changed.circulation (index + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega index ^ 2 * distance ^ 4)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_source_packet_deformation_arbitrary_budget amplitudePositive ratioBound rootPositive boundaryNonnegative
      (constant := 16384 / factor ^ 4 + 3072) (by positivity) tolerancePositive]
    with frequency frequencyOne budget index distance gap distancePositive gapLower
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have comparison := source_packet_physical_deformation_comparison
    (radius := changed.radius (index + 1))
    (changed.circulation_pos frequencyPositive ratioPositive (index + 1)).le
    (show 0 ≤ boundaryConstant / (scaleRoot ^ 2 * changed.omega (index + 1) ^ 2) by positivity)
    (show 0 < 2 * Real.sqrt 2 * changed.omega index by
      exact mul_pos (by positivity) (changed.omega_pos frequencyPositive ratioPositive index))
    distancePositive factorPositive gapLower
  exact comparison.trans (budget index distance distancePositive)

end EulerNonuniqueness.Paper
