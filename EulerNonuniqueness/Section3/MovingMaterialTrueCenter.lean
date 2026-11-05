import EulerNonuniqueness.Section3.MovingMaterialPatchMoments

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

theorem center_eq_centroid_of_average_velocity (path : MovingMaterialPatch) {horizon time : ℝ}
    (inside : time ∈ Icc 0 horizon) (initialInside : path.initialTime < 0) (finalInside : horizon < path.finalTime)
    (source : ℝ → Vorticity)
    (sourceIntegrable : ∀ parameter ∈ Icc 0 horizon, Integrable (source parameter))
    (sourceMembership : ∀ parameter ∈ Icc 0 horizon, MemLp (source parameter) (ENNReal.ofReal (4 : ℝ)) volume)
    (material : ∀ parameter ∈ Icc 0 horizon, ∀ label,
      path.boundaryVelocity parameter label = biotSavart (source parameter) (path.boundary parameter label))
    (averagedVelocity : ∀ parameter ∈ Icc 0 horizon,
      path.centerVelocity parameter = (volume.real (path.domain parameter))⁻¹ •
        ∫ position in path.domain parameter, biotSavart (source parameter) position)
    (initialCenter : path.center 0 = path.centroid 0) : path.center time = path.centroid time := by
  have differenceDerivative (parameter : ℝ) (member : parameter ∈ uIcc 0 time) :
      HasDerivAt (fun current => path.center current - path.centroid current) 0 parameter := by
    rw [uIcc_of_le inside.1] at member
    have closedInside : parameter ∈ Icc 0 horizon := ⟨member.1, member.2.trans inside.2⟩
    have centroidDerivative := path.centroid_hasDerivAt
      ⟨initialInside.trans_le closedInside.1, closedInside.2.trans_lt finalInside⟩
      (sourceIntegrable parameter closedInside) (sourceMembership parameter closedInside) (material parameter closedInside)
    have result := (path.center_equation parameter).sub centroidDerivative
    simpa only [averagedVelocity parameter closedInside, sub_self] using result
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt differenceDerivative
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume 0 time)
  simp only [intervalIntegral.integral_zero, initialCenter, sub_self, sub_zero] at identity
  exact sub_eq_zero.mp identity.symm

end EulerNonuniqueness.Paper.MovingMaterialPatch
