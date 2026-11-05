import EulerNonuniqueness.Section4.ReferenceCenterVelocity

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem quadrupoleCenter_relative_deriv_bound {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    {horizon time radius gap : ℝ} {strain : ℝ≥0}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (timeInside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count)
    (inside : ∀ patch : Fin 4, time ∈ Ioo
      (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label))
    (radiusNonnegative : 0 ≤ radius) (gapPositive : 0 < gap)
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
    ‖deriv (fun current => quadrupoleCenter family.patchMotion current index) time -
        biotSavart (externalPatchVorticity scales family.patchMotion time index)
          (quadrupoleCenter family.patchMotion time index)‖ ≤
      3 * (scales.circulation (index.val + 1) / (2 * Real.pi * gap)) + (strain : ℝ) * radius := by
  classical
  let average := fun patch : Fin 4 => patchAverageVelocity scales family.patchMotion time index patch
    (biotSavart (Paper.patchVorticity scales family.patchMotion time))
  let constant := biotSavart (externalPatchVorticity scales family.patchMotion time index)
    (quadrupoleCenter family.patchMotion time index)
  let bound := 3 * (scales.circulation (index.val + 1) / (2 * Real.pi * gap)) + (strain : ℝ) * radius
  have patchDerivative (patch : Fin 4) := family.patchCentroid_hasDerivAt evolution timeInside index patch
    (inside patch) (material patch)
  have derivative := (HasDerivAt.sum (u := Finset.univ) (fun patch _ => patchDerivative patch)).div_const (4 : ℂ)
  change HasDerivAt (fun current => quadrupoleCenter family.patchMotion current index)
    ((∑ patch : Fin 4, average patch) / 4) time at derivative
  have patchBound (patch : Fin 4) : ‖average patch - constant‖ ≤ bound :=
    evolution.patch_average_velocity_relative_bound timeInside amplitudePositive frequencyPositive ratioPositive index
      patch (quadrupoleCenter family.patchMotion time index) radiusNonnegative gapPositive sourceBounded
      (internalSeparated patch) distance positive separated strainBound
  have sumBound : ‖∑ patch : Fin 4, (average patch - constant)‖ ≤ 4 * bound := by
    apply (norm_sum_le (s := Finset.univ) (fun patch : Fin 4 => average patch - constant)).trans
    exact (Finset.sum_le_sum (fun patch _ => patchBound patch)).trans_eq (by simp)
  have identity : (∑ patch : Fin 4, average patch) / 4 - constant =
      (∑ patch : Fin 4, (average patch - constant)) / 4 := by
    simp only [Fin.sum_univ_succ]
    ring
  rw [derivative.deriv, identity, norm_div]
  have normFour : ‖(4 : ℂ)‖ = (4 : ℝ) := by norm_num
  rw [normFour]
  exact (div_le_div_of_nonneg_right sumBound (by norm_num)).trans_eq (by ring)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
