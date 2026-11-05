import EulerNonuniqueness.Section6.MovingPairedMemoryHistory
import EulerNonuniqueness.Section6.LaplaceGrowingErrorBound

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem centroidAsymmetry_paired_window_weighted_bound {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {finalTime start horizon hessian deformation decay radius : ℝ} {strain : ℝ≥0}
    (horizonNonnegative : 0 ≤ horizon) (hessianNonnegative : 0 ≤ hessian)
    (decayGap : 0 < decay - (strain : ℝ))
    (evolution : FinitePatchEvolution scales family.patchMotion finalTime)
    (finalTimePositive : 0 < finalTime)
    (timeRange : ∀ elapsed ∈ Icc 0 horizon, start + elapsed ∈ Icc 0 finalTime)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (inside : ∀ elapsed ∈ Icc 0 horizon, ∀ index,
      start + elapsed ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ elapsed ∈ Icc 0 horizon, ∀ index label,
      (family.patch index).boundaryVelocity (start + elapsed) label =
        biotSavart (family.vorticity (start + elapsed)) ((family.patch index).boundary (start + elapsed) label))
    (index : Fin count) (center : ℝ → ℂ) (radiusPositive : 0 < radius)
    (distance : ℝ → Fin count → ℝ)
    (positive : ∀ elapsed ∈ Icc 0 horizon, ∀ source ∈ Finset.univ.erase index, 0 < distance elapsed source)
    (separated : ∀ elapsed ∈ Icc 0 horizon, ∀ position ∈ Metric.closedBall (center elapsed) radius,
      ∀ source ∈ Finset.univ.erase index, ∀ patch,
      ∀ location ∈ family.patchMotion.domain (start + elapsed) source patch,
        distance elapsed source ≤ ‖position - location‖)
    (centroidsInside : ∀ elapsed ∈ Icc 0 horizon, ∀ patch,
      patchCentroid family.patchMotion (start + elapsed) index patch ∈ Metric.closedBall (center elapsed) radius)
    (firstPair : ∀ elapsed ∈ Icc 0 horizon,
      ‖patchCentroid family.patchMotion (start + elapsed) index 0 -
        patchCentroid family.patchMotion (start + elapsed) index 3‖ ≤ 2 * scales.length (index.val + 1))
    (secondPair : ∀ elapsed ∈ Icc 0 horizon,
      ‖patchCentroid family.patchMotion (start + elapsed) index 1 -
        patchCentroid family.patchMotion (start + elapsed) index 2‖ ≤ 2 * scales.length (index.val + 1))
    (control : ∀ elapsed ∈ Icc 0 horizon, ∀ patch,
      BoundaryCloseToCircle scales family.patchMotion (start + elapsed) index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (sourceBounded : ∀ elapsed ∈ Icc 0 horizon, ∀ source ∈ Finset.univ.erase index, ∀ patch,
      family.patchMotion.domain (start + elapsed) source patch ⊆ Metric.closedBall
        (patchCentroid family.patchMotion (start + elapsed) source patch) (2 * scales.radius (source.val + 1)))
    (receiverSmall : ∀ elapsed ∈ Icc 0 horizon, ∀ source ∈ Finset.univ.erase index,
      8 * scales.radius (index.val + 1) ≤ distance elapsed source)
    (sourceSmall : ∀ elapsed ∈ Icc 0 horizon, ∀ source ∈ Finset.univ.erase index,
      4 * scales.radius (source.val + 1) ≤ distance elapsed source)
    (centroidsSeparated : ∀ elapsed ∈ Icc 0 horizon, ∀ receiver,
      ∀ source ∈ Finset.univ.erase index, ∀ patch,
      distance elapsed source ≤ ‖patchCentroid family.patchMotion (start + elapsed) index receiver -
        patchCentroid family.patchMotion (start + elapsed) source patch‖)
    (strainBound : ∀ elapsed ∈ Icc 0 horizon,
      (∑ source ∈ Finset.univ.erase index,
        2 * scales.circulation (source.val + 1) / (Real.pi * distance elapsed source ^ 2)) ≤ (strain : ℝ))
    (hessianBound : ∀ elapsed ∈ Icc 0 horizon,
      (∑ source ∈ Finset.univ.erase index,
        4 * scales.circulation (source.val + 1) / (Real.pi * distance elapsed source ^ 3)) ≤ hessian) :
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
      ‖centroidAsymmetry family.patchMotion (start + elapsed) index‖) ≤
      hessian * (radius * scales.length (index.val + 1) +
        1024 * scales.radius (index.val + 1) ^ 2 * deformation) / (decay - (strain : ℝ)) ^ 2 +
      ‖centroidAsymmetry family.patchMotion start index‖ / (decay - (strain : ℝ)) := by
  let trajectory := fun elapsed => centroidAsymmetry family.patchMotion (start + elapsed) index
  let cost := hessian * (radius * scales.length (index.val + 1) +
    1024 * scales.radius (index.val + 1) ^ 2 * deformation)
  have lengthNonnegative := (scales.length_pos (index.val + 1)).le
  have trajectoryContinuous : Continuous trajectory := by
    unfold trajectory centroidAsymmetry
    exact (((((family.patchCentroid_continuous index 0).add
      (family.patchCentroid_continuous index 1)).sub
      (family.patchCentroid_continuous index 2)).sub
      (family.patchCentroid_continuous index 3)).div_const 4).comp (continuous_const.add continuous_id)
  have costNonnegative : 0 ≤ cost := by
    dsimp only [cost]
    positivity
  have localEstimate (elapsed : ℝ) (member : elapsed ∈ Icc 0 horizon) :
      HasDerivAt trajectory (deriv trajectory elapsed) elapsed ∧
        ‖deriv trajectory elapsed‖ ≤ (strain : ℝ) * ‖trajectory elapsed‖ + cost := by
    obtain ⟨derivative, errorBound⟩ := family.centroidAsymmetry_paired_external_equation scales
      densityEquation evolution finalTimePositive (timeRange elapsed member) amplitudePositive frequencyPositive
      ratioPositive (inside elapsed member) (material elapsed member) index (center elapsed) radiusPositive.le
      (distance elapsed) (positive elapsed member) (separated elapsed member) (centroidsInside elapsed member)
      (firstPair elapsed member) (secondPair elapsed member) (control elapsed member) nonnegative small
      (sourceBounded elapsed member) (receiverSmall elapsed member) (sourceSmall elapsed member)
      (centroidsSeparated elapsed member)
    have shifted := derivative.scomp elapsed ((hasDerivAt_id elapsed).const_add start)
    have shiftedDerivative : HasDerivAt trajectory
        (deriv (fun time => centroidAsymmetry family.patchMotion time index) (start + elapsed)) elapsed := by
      simpa [trajectory, Function.comp_def, derivative.deriv] using shifted
    have derivativeIdentity := shiftedDerivative.deriv
    rw [← derivativeIdentity] at errorBound
    let coefficient := ∑ source ∈ Finset.univ.erase index,
      4 * scales.circulation (source.val + 1) / (Real.pi * distance elapsed source ^ 3)
    have receiverIdentity : (4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
        (∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) / distance elapsed source ^ 3) =
        coefficient * (1024 * scales.radius (index.val + 1) ^ 2 * deformation) := by
      dsimp only [coefficient]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro source _
      ring
    rw [receiverIdentity] at errorBound
    have combined : coefficient * radius * scales.length (index.val + 1) +
        coefficient * (1024 * scales.radius (index.val + 1) ^ 2 * deformation) =
        coefficient * (radius * scales.length (index.val + 1) +
          1024 * scales.radius (index.val + 1) ^ 2 * deformation) := by ring
    rw [combined] at errorBound
    have refined := errorBound.trans (mul_le_mul_of_nonneg_right (hessianBound elapsed member)
      (by positivity : 0 ≤ radius * scales.length (index.val + 1) +
        1024 * scales.radius (index.val + 1) ^ 2 * deformation))
    have lipschitz := evolution.externalPatch_biotSavart_lipschitzOn (timeRange elapsed member)
      amplitudePositive frequencyPositive ratioPositive index (distance elapsed)
      (Metric.closedBall (center elapsed) radius) (positive elapsed member) (separated elapsed member)
      (strainBound elapsed member)
    have linearBound := norm_fderiv_le_of_lipschitzOn ℝ
      (Metric.closedBall_mem_nhds (center elapsed) radiusPositive) lipschitz
    let linear := fderiv ℝ (biotSavart (externalPatchVorticity scales family.patchMotion (start + elapsed) index))
      (center elapsed)
    refine ⟨shiftedDerivative.differentiableAt.hasDerivAt, ?_⟩
    calc
      _ = ‖linear (trajectory elapsed) + (deriv trajectory elapsed - linear (trajectory elapsed))‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add
        ((linear.le_opNorm _).trans (mul_le_mul_of_nonneg_right linearBound (norm_nonneg _))) refined)
  have history := norm_integral_gronwall trajectoryContinuous (continuous_const : Continuous (fun _ : ℝ => cost))
    strain.property horizonNonnegative
    (fun elapsed member => (localEstimate elapsed ⟨member.1, member.2.le⟩).1.hasDerivWithinAt)
    (fun elapsed member => (localEstimate elapsed ⟨member.1, member.2.le⟩).2)
  apply Section6.laplace_exponential_affine_norm_bound trajectoryContinuous decayGap costNonnegative
    (norm_nonneg _) horizonNonnegative
  intro elapsed member
  have integralBound := Section6.exponential_constant_history_integral_bound strain.property costNonnegative member.1
  change ‖trajectory elapsed‖ ≤ Real.exp ((strain : ℝ) * elapsed) *
    (cost * elapsed + ‖centroidAsymmetry family.patchMotion start index‖)
  have initialIdentity : trajectory 0 = centroidAsymmetry family.patchMotion start index := by simp [trajectory]
  rw [← initialIdentity]
  exact (history elapsed member).trans
    ((mul_le_mul_of_nonneg_left (add_le_add_left integralBound _) (Real.exp_pos _).le).trans_eq
      (congrArg (fun value => Real.exp ((strain : ℝ) * elapsed) * value) (add_comm _ _)))

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
