import EulerNonuniqueness.Section3.ExponentialStationaryChart
import EulerNonuniqueness.General.LinearExponentialCurve

namespace EulerNonuniqueness.General

noncomputable section

open Set Metric Filter
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

def exponentialStationaryMultiplier (generator : Space →L[ℝ] Space →L[ℝ] Space)
    (increment : Space) : Space →L[ℝ] Space := NormedSpace.exp ℝ (generator increment)

theorem exponentialStationaryMultiplier_continuous (generator : Space →L[ℝ] Space →L[ℝ] Space) :
    Continuous (exponentialStationaryMultiplier generator) :=
  (NormedSpace.exp_continuous (𝕂 := ℝ)).comp generator.continuous

theorem exponentialStationaryMultiplier_zero (generator : Space →L[ℝ] Space →L[ℝ] Space) :
    exponentialStationaryMultiplier generator 0 = ContinuousLinearMap.id ℝ Space := by
  simp only [exponentialStationaryMultiplier, map_zero, NormedSpace.exp_zero, ContinuousLinearMap.one_def]

theorem exponentialStationaryMultiplier_apply_eq_curve
    (generator : Space →L[ℝ] Space →L[ℝ] Space) (increment base : Space) :
    exponentialStationaryMultiplier generator increment base = linearExponentialCurve (generator increment) base 1 := by
  simp only [exponentialStationaryMultiplier, linearExponentialCurve, one_smul]

theorem exponentialStationaryMultiplier_exists_norm_bound
    (generator : Space →L[ℝ] Space →L[ℝ] Space) :
    ∃ radius > 0, ∀ increment : Space, ‖increment‖ ≤ radius →
      ‖exponentialStationaryMultiplier generator increment‖ ≤ 2 := by
  have continuousNorm := (exponentialStationaryMultiplier_continuous generator).norm
  have zeroBound : ‖exponentialStationaryMultiplier generator 0‖ < 2 := by
    rw [exponentialStationaryMultiplier_zero]
    exact (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℝ Space‖ ≤ 1).trans_lt (by norm_num)
  have nearby : {increment : Space | ‖exponentialStationaryMultiplier generator increment‖ < 2} ∈ 𝓝 (0 : Space) :=
    (continuousNorm.tendsto 0).eventually (eventually_lt_nhds zeroBound)
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp nearby
  refine ⟨radius / 2, by positivity, ?_⟩
  intro increment small
  have inside : increment ∈ ball (0 : Space) radius := by
    rw [mem_ball_zero_iff]
    exact small.trans_lt (by linarith)
  exact (contained inside).le

theorem exponentialStationaryChart_sub_multiplier
    (generator : Space →L[ℝ] Space →L[ℝ] Space) (base increment : Space) :
    exponentialStationaryChart generator base increment - exponentialStationaryMultiplier generator increment base =
      exponentialStationaryMultiplier generator increment (increment - generator increment base) := by
  unfold exponentialStationaryChart exponentialStationaryMultiplier
  rw [map_sub, map_add, map_sub]
  abel

theorem exponentialStationaryChart_exists_relabel_defect_bound
    (generator : Space →L[ℝ] Space →L[ℝ] Space) (base : Space) :
    ∃ radius > 0, ∀ increment : Space, ‖increment‖ ≤ radius →
      ‖exponentialStationaryChart generator base increment - exponentialStationaryMultiplier generator increment base‖ ≤
        2 * ‖increment - generator increment base‖ := by
  obtain ⟨radius, positive, bounded⟩ := exponentialStationaryMultiplier_exists_norm_bound generator
  refine ⟨radius, positive, ?_⟩
  intro increment small
  rw [exponentialStationaryChart_sub_multiplier]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (bounded increment small) (norm_nonneg _))

end

end EulerNonuniqueness.General
