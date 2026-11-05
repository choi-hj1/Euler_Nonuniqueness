import EulerNonuniqueness.Section4.ReferenceAngularFlux
import EulerNonuniqueness.Section4.ReferenceCenterDynamics

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem quadrupole_angularImpulse_deriv_closed_bound {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon time radius gap : ℝ} {strain : ℝ≥0}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (timeInside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (inside : ∀ index, time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ index label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (index : Fin count) (radiusNonnegative : 0 ≤ radius) (gapPositive : 0 < gap)
    (sourceBounded : ∀ patch, family.patchMotion.domain time index patch ⊆
      Metric.closedBall (quadrupoleCenter family.patchMotion time index) radius)
    (internalSeparated : ∀ receiver source : Fin 4, source ≠ receiver →
      ∀ position ∈ family.patchMotion.domain time index receiver,
      ∀ location ∈ family.patchMotion.domain time index source, gap ≤ ‖position - location‖)
    (distance : Fin count → ℝ)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ position ∈ Metric.closedBall (quadrupoleCenter family.patchMotion time index) radius,
      ∀ source ∈ Finset.univ.erase index, ∀ patch,
      ∀ location ∈ family.patchMotion.domain time source patch, distance source ≤ ‖position - location‖)
    (strainBound : (∑ source ∈ Finset.univ.erase index,
      2 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 2)) ≤ (strain : ℝ)) :
    |deriv (fun current => angularImpulse scales family.patchMotion current index) time| ≤
      8 * scales.circulation (index.val + 1) * ‖centroidAsymmetry family.patchMotion time index‖ *
        (3 * (scales.circulation (index.val + 1) / (2 * Real.pi * gap)) + (strain : ℝ) * radius) +
      8 * scales.circulation (index.val + 1) * (strain : ℝ) * radius ^ 2 := by
  have angular := family.quadrupole_angularImpulse_deriv_bound scales densityEquation evolution timeInside
    amplitudePositive frequencyPositive ratioPositive inside material index radiusNonnegative sourceBounded
    distance positive separated strainBound
  have center := family.quadrupoleCenter_relative_deriv_bound scales evolution timeInside amplitudePositive
    frequencyPositive ratioPositive index (fun patch => inside _) (by
      intro patch label
      rw [family.patchVorticity_eq scales densityEquation]
      exact material _ label) radiusNonnegative gapPositive sourceBounded internalSeparated distance positive
    separated strainBound
  rw [norm_sub_rev] at center
  exact angular.trans (add_le_add_right (mul_le_mul_of_nonneg_left center
    (mul_nonneg (mul_nonneg (by norm_num)
      (scales.circulation_pos frequencyPositive ratioPositive _).le) (norm_nonneg _))) _)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
