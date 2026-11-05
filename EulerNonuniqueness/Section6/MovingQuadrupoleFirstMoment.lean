import EulerNonuniqueness.Section6.MovingQuadrupoleAngularMoment
import EulerNonuniqueness.Section6.PaperQuadrupoleStaticMoments

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

theorem quadrupole_first_moment_hasDerivAt_external
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {time : ℝ}
    (inside : ∀ index, time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ index label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (index : Fin count) :
    HasDerivAt (fun parameter => ∫ position,
      quadrupoleDensity scales family.patchMotion parameter index position • position)
      (∫ position, quadrupoleDensity scales family.patchMotion time index position •
        (biotSavart (family.vorticity time) position -
          biotSavart (quadrupoleDensity scales family.patchMotion time index) position)) time := by
  simp_rw [family.quadrupoleDensity_eq_subfamily scales densityEquation]
  exact family.subfamily_first_moment_hasDerivAt_external (quadrupolePatchLabels index) inside material

theorem centroidAsymmetry_hasDerivAt_external
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon time : ℝ} (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (timeInside : time ∈ Ioo 0 horizon)
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
  have positive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  apply derivative.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds timeInside] with parameter member
  have identity := evolution.integral_quadrupoleDensity_first_moment
    ⟨member.1.le, member.2.le⟩ amplitudePositive frequencyPositive ratioPositive index 0
  simp only [sub_zero] at identity
  rw [identity, smul_smul, inv_mul_cancel₀ (ne_of_gt (mul_pos (by norm_num) positive)), one_smul]

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
