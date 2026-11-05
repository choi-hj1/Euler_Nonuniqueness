import EulerNonuniqueness.Section4.ReferenceCoMovingPairPreservation
import EulerNonuniqueness.Section1.UniformTransportScaleSmallness

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_reference_comoving_numeric (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) :
    ∀ᶠ frequency : ℝ in atTop,
      2 * ((15120 / Real.pi) * ({scales with frequency := frequency}).strain +
        1800 * (1 / 57600)) ≤ 1 / 4 ∧
      ∀ index : ℕ, ({scales with frequency := frequency}).omega index *
          ({scales with frequency := frequency}).length index ≤ (1 / 57600) * scales.location index := by
  have strainSmall := (scales.strain_tendsto_zero ratioBound alphaPositive).eventually
    (eventually_lt_nhds (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 241920)))
  have transportSmall := scales.eventually_omega_length_lt_location ratioBound alphaPositive
    (by norm_num : (0 : ℝ) < 1 / 57600)
  filter_upwards [strainSmall, transportSmall] with frequency strainSmall transportSmall
  refine ⟨?_, fun index => (transportSmall index).le⟩
  calc
    _ ≤ 2 * ((15120 / Real.pi) * (Real.pi / 241920) + 1800 * (1 / 57600)) := by
      gcongr
    _ = (3 : ℝ) / 16 := by field_simp; norm_num
    _ ≤ 1 / 4 := by norm_num

end EulerNonuniqueness.Paper
