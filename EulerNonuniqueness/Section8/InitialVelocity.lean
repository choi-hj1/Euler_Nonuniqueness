import EulerNonuniqueness.Section8.VelocityContinuity

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace EulerNonuniqueness

theorem InitialDatum.exists_support_radius {initial : Vorticity} (datum : InitialDatum initial) :
    ∃ radius : ℝ, 0 < radius ∧ Function.support initial ⊆ Metric.closedBall 0 radius := by
  obtain ⟨radius, positive, bounded⟩ := datum.1.isCompact.isBounded.exists_pos_norm_le
  refine ⟨radius, positive, ?_⟩
  intro position inside
  simpa only [Metric.mem_closedBall, dist_zero_right] using bounded position (subset_tsupport initial inside)

theorem InitialDatum.biotSavart_memLp_two {initial : Vorticity} (datum : InitialDatum initial) :
    MemLp (biotSavart initial) 2 volume := by
  obtain ⟨radius, positive, supported⟩ := datum.exists_support_radius
  have integrable : Integrable initial := memLp_one_iff_integrable.mp (by simpa using datum.2.1 1 le_rfl)
  exact memLp_biotSavart_two_of_memLp_support_integral_zero holderConjugate_four_fourThirds
    (datum.2.1 4 (by norm_num)) (by norm_num) integrable datum.2.2 positive.le supported

theorem InitialDatum.continuous_biotSavart {initial : Vorticity} (datum : InitialDatum initial) :
    Continuous (biotSavart initial) := by
  obtain ⟨radius, positive, supported⟩ := datum.exists_support_radius
  exact continuous_biotSavart_of_memLp_support holderConjugate_four_fourThirds
    (datum.2.1 4 (by norm_num)) (by norm_num) positive.le supported

end EulerNonuniqueness
