import EulerNonuniqueness.Section6.MovingQuadrupoleEndpointMoment
import EulerNonuniqueness.Section6.PaperNeutralTaylorRemainder

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

theorem centroidAsymmetry_external_linearization_closed
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon time radius : ℝ} (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (horizonPositive : 0 < horizon) (timeInside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (inside : ∀ index, time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ index label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (index : Fin count) (center : ℂ) (radiusNonnegative : 0 ≤ radius)
    (sourceBounded : ∀ patch, family.patchMotion.domain time index patch ⊆ Metric.closedBall center radius)
    (distance : Fin count → ℝ)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ patch,
      ∀ location ∈ family.patchMotion.domain time source patch, distance source ≤ ‖center - location‖)
    (near : ∀ source ∈ Finset.univ.erase index, 2 * radius ≤ distance source) :
    ∃ error : ℂ,
      HasDerivAt (fun parameter => centroidAsymmetry family.patchMotion parameter index)
        (fderiv ℝ (biotSavart (externalPatchVorticity scales family.patchMotion time index)) center
          (centroidAsymmetry family.patchMotion time index) + error) time ∧
      ‖error‖ ≤ (∑ source ∈ Finset.univ.erase index,
        4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) * radius ^ 2 := by
  let coefficient := 4 * scales.circulation (index.val + 1)
  let linear := fderiv ℝ (biotSavart (externalPatchVorticity scales family.patchMotion time index)) center
  let remainder := ∫ position, quadrupoleDensity scales family.patchMotion time index position •
    (biotSavart (externalPatchVorticity scales family.patchMotion time index) position -
      biotSavart (externalPatchVorticity scales family.patchMotion time index) center - linear (position - center))
  have coefficientPositive : 0 < coefficient :=
    mul_pos (by norm_num) (scales.circulation_pos frequencyPositive ratioPositive _)
  have timeClosed : time ∈ Icc 0 horizon := timeInside
  have fieldIdentity (position : ℂ) : biotSavart (family.vorticity time) position -
      biotSavart (quadrupoleDensity scales family.patchMotion time index) position =
      biotSavart (externalPatchVorticity scales family.patchMotion time index) position := by
    rw [← family.patchVorticity_eq scales densityEquation,
      evolution.patchVorticity_biotSavart_internal_external timeClosed index position,
      evolution.quadrupole_biotSavart_eq_sum_patch timeClosed index position]
    abel
  have derivative := family.centroidAsymmetry_hasDerivAt_external_closed scales densityEquation evolution
    horizonPositive timeInside amplitudePositive frequencyPositive ratioPositive inside material index
  simp_rw [fieldIdentity] at derivative
  have identity := evolution.quadrupole_external_first_moment_taylor_identity timeClosed
    amplitudePositive frequencyPositive ratioPositive index center
  have expansion : (∫ position, quadrupoleDensity scales family.patchMotion time index position •
      biotSavart (externalPatchVorticity scales family.patchMotion time index) position) =
      linear (coefficient • centroidAsymmetry family.patchMotion time index) + remainder := by
    exact (sub_eq_iff_eq_add.mp identity).trans (add_comm _ _)
  refine ⟨coefficient⁻¹ • remainder, ?_, ?_⟩
  · have rateIdentity : coefficient⁻¹ • (∫ position,
        quadrupoleDensity scales family.patchMotion time index position •
          biotSavart (externalPatchVorticity scales family.patchMotion time index) position) =
        linear (centroidAsymmetry family.patchMotion time index) + coefficient⁻¹ • remainder := by
      rw [expansion, smul_add, linear.map_smul, smul_smul,
        inv_mul_cancel₀ coefficientPositive.ne', one_smul]
    rw [rateIdentity] at derivative
    exact derivative
  · have bound := evolution.quadrupole_external_taylor_remainder_bound timeClosed
      amplitudePositive frequencyPositive ratioPositive index center radiusNonnegative
      sourceBounded distance positive separated near
    change ‖remainder‖ ≤ coefficient * (∑ source ∈ Finset.univ.erase index,
      4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) * radius ^ 2 at bound
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr coefficientPositive)]
    have multiplied := mul_le_mul_of_nonneg_left bound (inv_pos.mpr coefficientPositive).le
    exact multiplied.trans_eq (by field_simp; ring)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily

