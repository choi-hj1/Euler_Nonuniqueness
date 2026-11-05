import EulerNonuniqueness.Section6.MovingQuadrupoleEndpointMoment
import EulerNonuniqueness.Section6.PaperPairedNeutralMemory

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

theorem centroidAsymmetry_paired_external_equation
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon time radius length deformation : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (horizonPositive : 0 < horizon) (timeInside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (inside : ∀ index, time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ index label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (index : Fin count) (center : ℂ) (radiusNonnegative : 0 ≤ radius) (distance : Fin count → ℝ)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ position ∈ Metric.closedBall center radius,
      ∀ source ∈ Finset.univ.erase index, ∀ patch, ∀ location ∈ family.patchMotion.domain time source patch,
        distance source ≤ ‖position - location‖)
    (centroidsInside : ∀ patch, patchCentroid family.patchMotion time index patch ∈ Metric.closedBall center radius)
    (firstPair : ‖patchCentroid family.patchMotion time index 0 - patchCentroid family.patchMotion time index 3‖ ≤ 2 * length)
    (secondPair : ‖patchCentroid family.patchMotion time index 1 - patchCentroid family.patchMotion time index 2‖ ≤ 2 * length)
    (control : ∀ patch, BoundaryCloseToCircle scales family.patchMotion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (sourceBounded : ∀ source ∈ Finset.univ.erase index, ∀ patch, family.patchMotion.domain time source patch ⊆
      Metric.closedBall (patchCentroid family.patchMotion time source patch) (2 * scales.radius (source.val + 1)))
    (receiverSmall : ∀ source ∈ Finset.univ.erase index, 8 * scales.radius (index.val + 1) ≤ distance source)
    (sourceSmall : ∀ source ∈ Finset.univ.erase index, 4 * scales.radius (source.val + 1) ≤ distance source)
    (centroidsSeparated : ∀ receiver, ∀ source ∈ Finset.univ.erase index, ∀ patch,
      distance source ≤ ‖patchCentroid family.patchMotion time index receiver - patchCentroid family.patchMotion time source patch‖) :
    HasDerivAt (fun parameter => centroidAsymmetry family.patchMotion parameter index)
      ((4 * scales.circulation (index.val + 1))⁻¹ •
        ∫ position, quadrupoleDensity scales family.patchMotion time index position •
          biotSavart (externalPatchVorticity scales family.patchMotion time index) position) time ∧
    ‖deriv (fun parameter => centroidAsymmetry family.patchMotion parameter index) time -
        fderiv ℝ (biotSavart (externalPatchVorticity scales family.patchMotion time index)) center
          (centroidAsymmetry family.patchMotion time index)‖ ≤
      (∑ source ∈ Finset.univ.erase index,
        4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) * radius * length +
      (4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
        ∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) / distance source ^ 3 := by
  have derivative := family.centroidAsymmetry_hasDerivAt_external_closed scales densityEquation evolution
    horizonPositive timeInside amplitudePositive frequencyPositive ratioPositive inside material index
  have fieldIdentity (position : ℂ) : biotSavart (family.vorticity time) position -
      biotSavart (quadrupoleDensity scales family.patchMotion time index) position =
      biotSavart (externalPatchVorticity scales family.patchMotion time index) position := by
    rw [← family.patchVorticity_eq scales densityEquation,
      evolution.patchVorticity_biotSavart_internal_external timeInside index position,
      evolution.quadrupole_biotSavart_eq_sum_patch timeInside index position]
    abel
  simp_rw [fieldIdentity] at derivative
  refine ⟨derivative, ?_⟩
  rw [derivative.deriv]
  exact evolution.quadrupole_paired_neutral_memory_rate_bound timeInside amplitudePositive
    frequencyPositive ratioPositive index center radiusNonnegative distance positive separated
    centroidsInside firstPair secondPair control nonnegative small sourceBounded receiverSmall
    sourceSmall centroidsSeparated

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
