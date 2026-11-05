import EulerNonuniqueness.Section6.MovingQuadrupoleFirstMoment

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

theorem centroidAsymmetry_hasDerivAt_external_closed
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon time : ℝ} (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (horizonPositive : 0 < horizon) (timeInside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (inside : ∀ index, time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ index label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (index : Fin count) :
    HasDerivAt (fun parameter => centroidAsymmetry family.patchMotion parameter index)
      ((4 * scales.circulation (index.val + 1))⁻¹ •
        ∫ position, quadrupoleDensity scales family.patchMotion time index position •
          (biotSavart (family.vorticity time) position -
            biotSavart (quadrupoleDensity scales family.patchMotion time index) position)) time := by
  have derivative := (family.quadrupole_first_moment_hasDerivAt_external scales densityEquation
    inside material index).const_smul ((4 * scales.circulation (index.val + 1))⁻¹)
  have coefficientPositive : 0 < 4 * scales.circulation (index.val + 1) :=
    mul_pos (by norm_num) (scales.circulation_pos frequencyPositive ratioPositive _)
  have equality (parameter : ℝ) (member : parameter ∈ Icc 0 horizon) :
      centroidAsymmetry family.patchMotion parameter index =
      (4 * scales.circulation (index.val + 1))⁻¹ •
        ∫ position, quadrupoleDensity scales family.patchMotion parameter index position • position := by
    have identity := evolution.integral_quadrupoleDensity_first_moment member
      amplitudePositive frequencyPositive ratioPositive index 0
    simp only [sub_zero] at identity
    rw [identity, smul_smul, inv_mul_cancel₀ coefficientPositive.ne', one_smul]
  have within := derivative.hasDerivWithinAt.congr equality (equality time timeInside)
  have differentiable : DifferentiableAt ℝ
      (fun parameter => centroidAsymmetry family.patchMotion parameter index) time := by
    unfold centroidAsymmetry
    exact ((((family.patchCentroid_differentiableAt inside material index 0).add
      (family.patchCentroid_differentiableAt inside material index 1)).sub
      (family.patchCentroid_differentiableAt inside material index 2)).sub
      (family.patchCentroid_differentiableAt inside material index 3)).div_const 4
  have rate := (uniqueDiffOn_Icc horizonPositive time timeInside).eq_deriv (Icc 0 horizon)
    differentiable.hasDerivAt.hasDerivWithinAt within
  rw [← rate]
  exact differentiable.hasDerivAt

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
