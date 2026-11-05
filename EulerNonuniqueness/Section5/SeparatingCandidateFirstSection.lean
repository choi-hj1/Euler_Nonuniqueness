import EulerNonuniqueness.Section5.SeparatingCandidateRadiusDynamics

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section2

theorem separatingCandidate_exists_first_section
    (timeShift rotationPhase dipoleAngle : ℝ) (offset : ℂ) (incoming radiusMin : ℝ) :
    let radius := fun time => ‖(separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time -
      (separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time‖
    let velocity := fun time => separatingRadiusScalarVelocity (separatingScalarOrbit 1 (by norm_num) (time + timeShift))
    ∃ sectionTime : ℝ, max (incoming + 1) 0 < sectionTime ∧ radiusMin ≤ radius sectionTime ∧
      (∀ time ∈ Icc (sectionTime - 1) (sectionTime + 1),
        HasDerivAt radius (velocity time) time ∧ 1 ≤ velocity time) ∧
      ∀ time ≤ sectionTime - 1, radius time ≤ radius sectionTime - 1 := by
  let radius := fun time => ‖(separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time -
    (separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time‖
  let velocity := fun time => separatingRadiusScalarVelocity (separatingScalarOrbit 1 (by norm_num) (time + timeShift))
  obtain ⟨derivative, increasing, _, eventualLower⟩ :=
    separatingCandidate_radius_dynamics timeShift rotationPhase dipoleAngle offset
  obtain ⟨tailStart, lower⟩ := eventually_atTop.mp eventualLower
  have continuous : Continuous radius :=
    continuous_iff_continuousAt.mpr (fun time => (derivative time).continuousAt)
  have growth {first second : ℝ} (firstAbove : tailStart ≤ first) (ordered : first ≤ second) :
      second - first ≤ radius second - radius first := by
    rcases eq_or_lt_of_le ordered with equal | strict
    · subst second
      simp only [sub_self, le_refl]
    obtain ⟨time, member, derivativeSlope⟩ := exists_hasDerivAt_eq_slope radius velocity strict
      continuous.continuousOn (fun time _ => derivative time)
    have slopeLower : 1 ≤ (radius second - radius first) / (second - first) :=
      (lower time (firstAbove.trans member.1.le)).trans_eq derivativeSlope
    simpa only [one_mul] using (le_div_iff₀ (sub_pos.mpr strict)).mp slopeLower
  let sectionTime := max (max (incoming + 1) 0 + 1)
    (max (tailStart + 1) (tailStart + radiusMin - radius tailStart))
  have sectionStrict : max (incoming + 1) 0 < sectionTime := by
    have bound : max (incoming + 1) 0 + 1 ≤ sectionTime := le_max_left _ _
    linarith only [bound]
  have sectionAbove : tailStart + 1 ≤ sectionTime :=
    (le_max_left _ _).trans (le_max_right _ _)
  have sectionLevel : tailStart + radiusMin - radius tailStart ≤ sectionTime :=
    (le_max_right _ _).trans (le_max_right _ _)
  have sectionRadius : radiusMin ≤ radius sectionTime := by
    have bound := growth le_rfl (by linarith only [sectionAbove] : tailStart ≤ sectionTime)
    linarith only [bound, sectionLevel]
  have sectionMargin : radius (sectionTime - 1) ≤ radius sectionTime - 1 := by
    have bound := growth (by linarith only [sectionAbove] : tailStart ≤ sectionTime - 1)
      (by linarith : sectionTime - 1 ≤ sectionTime)
    linarith only [bound]
  refine ⟨sectionTime, sectionStrict, sectionRadius, ?_, ?_⟩
  · intro time member
    exact ⟨derivative time, lower time (by linarith only [sectionAbove, member.1])⟩
  · intro time before
    exact (increasing.monotone before).trans sectionMargin

end EulerNonuniqueness.Paper
