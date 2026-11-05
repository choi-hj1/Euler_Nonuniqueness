import EulerNonuniqueness.Section3.FiniteMovingPatchTransport

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

theorem domain_area_eq_initial (family : FiniteMovingPatchFamily count) {horizon time : ℝ}
    (inside : time ∈ Icc 0 horizon)
    (initialInside : ∀ index, (family.patch index).initialTime < 0)
    (finalInside : ∀ index, horizon < (family.patch index).finalTime)
    (material : ∀ parameter ∈ Icc 0 horizon, ∀ index label,
      (family.patch index).boundaryVelocity parameter label =
        biotSavart (family.vorticity parameter) ((family.patch index).boundary parameter label)) (index : Fin count) :
    volume.real ((family.patch index).domain time) = volume.real ((family.patch index).domain 0) := by
  have derivative (parameter : ℝ) (member : parameter ∈ uIcc 0 time) :
      HasDerivAt (fun current => volume.real ((family.patch index).domain current)) 0 parameter := by
    rw [uIcc_of_le inside.1] at member
    have closedInside : parameter ∈ Icc 0 horizon := ⟨member.1, member.2.trans inside.2⟩
    exact (family.patch index).domain_area_hasDerivAt
      ⟨(initialInside index).trans_le closedInside.1, closedInside.2.trans_lt (finalInside index)⟩
      (family.vorticity_integrable parameter) (family.vorticity_memLp parameter _) (material parameter closedInside index)
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 time)
  simp only [intervalIntegral.integral_zero] at identity
  linarith

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
