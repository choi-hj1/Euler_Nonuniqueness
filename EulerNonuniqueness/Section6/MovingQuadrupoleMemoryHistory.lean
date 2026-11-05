import EulerNonuniqueness.Section6.MovingQuadrupoleClosedMemory
import EulerNonuniqueness.Section6.MovingComplexMomentContinuity
import EulerNonuniqueness.General.NormIntegralGronwall

noncomputable section

open Set MeasureTheory
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

theorem centroidAsymmetry_memory_history_bound
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon finish hessian : ℝ} {strain : ℝ≥0}
    (radius : ℝ → ℝ) (radiusContinuous : Continuous radius) (finishNonnegative : 0 ≤ finish)
    (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (horizonPositive : 0 < horizon) (timeRange : Icc 0 finish ⊆ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (inside : ∀ time ∈ Icc 0 finish, ∀ index,
      time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ time ∈ Icc 0 finish, ∀ index label,
      (family.patch index).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (index : Fin count) (center : ℝ → ℂ) (radiusNonnegative : ∀ time ∈ Icc 0 finish, 0 ≤ radius time)
    (sourceBounded : ∀ time ∈ Icc 0 finish, ∀ patch,
      family.patchMotion.domain time index patch ⊆ Metric.closedBall (center time) (radius time))
    (distance : ℝ → Fin count → ℝ) (region : ℝ → Set ℂ)
    (neighborhood : ∀ time ∈ Icc 0 finish, region time ∈ 𝓝 (center time))
    (positive : ∀ time ∈ Icc 0 finish, ∀ source ∈ Finset.univ.erase index, 0 < distance time source)
    (separated : ∀ time ∈ Icc 0 finish, ∀ position ∈ region time,
      ∀ source ∈ Finset.univ.erase index, ∀ patch,
      ∀ location ∈ family.patchMotion.domain time source patch,
        distance time source ≤ ‖position - location‖)
    (near : ∀ time ∈ Icc 0 finish, ∀ source ∈ Finset.univ.erase index,
      2 * radius time ≤ distance time source)
    (strainBound : ∀ time ∈ Icc 0 finish,
      (∑ source ∈ Finset.univ.erase index,
        2 * scales.circulation (source.val + 1) / (Real.pi * distance time source ^ 2)) ≤ (strain : ℝ))
    (hessianBound : ∀ time ∈ Icc 0 finish,
      (∑ source ∈ Finset.univ.erase index,
        4 * scales.circulation (source.val + 1) / (Real.pi * distance time source ^ 3)) ≤ hessian) :
    ∀ time ∈ Icc 0 finish,
      ‖centroidAsymmetry family.patchMotion time index‖ ≤
        Real.exp ((strain : ℝ) * time) *
          (‖centroidAsymmetry family.patchMotion 0 index‖ +
            ∫ current in (0 : ℝ)..time, Real.exp (-(strain : ℝ) * current) * (hessian * radius current ^ 2)) := by
  have continuous : Continuous (fun time => centroidAsymmetry family.patchMotion time index) := by
    unfold centroidAsymmetry
    exact ((((family.patchCentroid_continuous index 0).add
      (family.patchCentroid_continuous index 1)).sub
      (family.patchCentroid_continuous index 2)).sub
      (family.patchCentroid_continuous index 3)).div_const 4
  have localEstimate (time : ℝ) (member : time ∈ Icc 0 finish) :
      HasDerivAt (fun parameter => centroidAsymmetry family.patchMotion parameter index)
        (deriv (fun parameter => centroidAsymmetry family.patchMotion parameter index) time) time ∧
      ‖deriv (fun parameter => centroidAsymmetry family.patchMotion parameter index) time‖ ≤
        (strain : ℝ) * ‖centroidAsymmetry family.patchMotion time index‖ + hessian * radius time ^ 2 := by
    obtain ⟨error, derivative, errorBound⟩ := family.centroidAsymmetry_external_linearization_closed
      scales densityEquation evolution horizonPositive (timeRange member) amplitudePositive frequencyPositive
      ratioPositive (inside time member) (material time member) index (center time) (radiusNonnegative time member)
      (sourceBounded time member) (distance time) (positive time member)
      (separated time member (center time) (mem_of_mem_nhds (neighborhood time member))) (near time member)
    have lipschitz := evolution.externalPatch_biotSavart_lipschitzOn (timeRange member)
      amplitudePositive frequencyPositive ratioPositive index (distance time) (region time)
      (positive time member) (separated time member) (strainBound time member)
    have linearBound := norm_fderiv_le_of_lipschitzOn ℝ (neighborhood time member) lipschitz
    refine ⟨derivative.differentiableAt.hasDerivAt, ?_⟩
    rw [derivative.deriv]
    exact (norm_add_le _ _).trans (add_le_add
      (((fderiv ℝ (biotSavart (externalPatchVorticity scales family.patchMotion time index))
        (center time)).le_opNorm _).trans (mul_le_mul_of_nonneg_right linearBound (norm_nonneg _)))
      (errorBound.trans (mul_le_mul_of_nonneg_right (hessianBound time member) (sq_nonneg (radius time)))))
  exact norm_integral_gronwall continuous
    (continuous_const.mul (radiusContinuous.pow 2)) strain.property finishNonnegative
    (fun time member => (localEstimate time ⟨member.1, member.2.le⟩).1.hasDerivWithinAt)
    (fun time member => (localEstimate time ⟨member.1, member.2.le⟩).2)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily

