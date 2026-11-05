import EulerNonuniqueness.Section6.MovingPairedNeutralMemory
import EulerNonuniqueness.Section6.MovingComplexMomentContinuity
import EulerNonuniqueness.General.NormIntegralGronwall

noncomputable section

open Set MeasureTheory
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

theorem centroidAsymmetry_paired_memory_history
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon finish hessian deformation : ℝ} {strain : ℝ≥0}
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
    (index : Fin count) (center : ℝ → ℂ) (radiusPositive : ∀ time ∈ Icc 0 finish, 0 < radius time)
    (distance : ℝ → Fin count → ℝ)
    (positive : ∀ time ∈ Icc 0 finish, ∀ source ∈ Finset.univ.erase index, 0 < distance time source)
    (separated : ∀ time ∈ Icc 0 finish, ∀ position ∈ Metric.closedBall (center time) (radius time),
      ∀ source ∈ Finset.univ.erase index, ∀ patch,
      ∀ location ∈ family.patchMotion.domain time source patch, distance time source ≤ ‖position - location‖)
    (centroidsInside : ∀ time ∈ Icc 0 finish, ∀ patch,
      patchCentroid family.patchMotion time index patch ∈ Metric.closedBall (center time) (radius time))
    (firstPair : ∀ time ∈ Icc 0 finish,
      ‖patchCentroid family.patchMotion time index 0 - patchCentroid family.patchMotion time index 3‖ ≤
        2 * scales.length (index.val + 1))
    (secondPair : ∀ time ∈ Icc 0 finish,
      ‖patchCentroid family.patchMotion time index 1 - patchCentroid family.patchMotion time index 2‖ ≤
        2 * scales.length (index.val + 1))
    (control : ∀ time ∈ Icc 0 finish, ∀ patch,
      BoundaryCloseToCircle scales family.patchMotion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (sourceBounded : ∀ time ∈ Icc 0 finish, ∀ source ∈ Finset.univ.erase index, ∀ patch,
      family.patchMotion.domain time source patch ⊆ Metric.closedBall
        (patchCentroid family.patchMotion time source patch) (2 * scales.radius (source.val + 1)))
    (receiverSmall : ∀ time ∈ Icc 0 finish, ∀ source ∈ Finset.univ.erase index,
      8 * scales.radius (index.val + 1) ≤ distance time source)
    (sourceSmall : ∀ time ∈ Icc 0 finish, ∀ source ∈ Finset.univ.erase index,
      4 * scales.radius (source.val + 1) ≤ distance time source)
    (centroidsSeparated : ∀ time ∈ Icc 0 finish, ∀ receiver, ∀ source ∈ Finset.univ.erase index, ∀ patch,
      distance time source ≤ ‖patchCentroid family.patchMotion time index receiver -
        patchCentroid family.patchMotion time source patch‖)
    (strainBound : ∀ time ∈ Icc 0 finish,
      (∑ source ∈ Finset.univ.erase index,
        2 * scales.circulation (source.val + 1) / (Real.pi * distance time source ^ 2)) ≤ (strain : ℝ))
    (hessianBound : ∀ time ∈ Icc 0 finish,
      (∑ source ∈ Finset.univ.erase index,
        4 * scales.circulation (source.val + 1) / (Real.pi * distance time source ^ 3)) ≤ hessian) :
    ∀ time ∈ Icc 0 finish, ‖centroidAsymmetry family.patchMotion time index‖ ≤
      Real.exp ((strain : ℝ) * time) * (‖centroidAsymmetry family.patchMotion 0 index‖ +
        ∫ current in (0 : ℝ)..time, Real.exp (-(strain : ℝ) * current) *
          (hessian * (radius current * scales.length (index.val + 1) +
            1024 * scales.radius (index.val + 1) ^ 2 * deformation))) := by
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
        (strain : ℝ) * ‖centroidAsymmetry family.patchMotion time index‖ +
          hessian * (radius time * scales.length (index.val + 1) +
            1024 * scales.radius (index.val + 1) ^ 2 * deformation) := by
    obtain ⟨derivative, errorBound⟩ := family.centroidAsymmetry_paired_external_equation scales
      densityEquation evolution horizonPositive (timeRange member) amplitudePositive frequencyPositive ratioPositive
      (inside time member) (material time member) index (center time) (radiusPositive time member).le
      (distance time) (positive time member) (separated time member) (centroidsInside time member)
      (firstPair time member) (secondPair time member) (control time member) nonnegative small
      (sourceBounded time member) (receiverSmall time member) (sourceSmall time member) (centroidsSeparated time member)
    let linear := fderiv ℝ (biotSavart (externalPatchVorticity scales family.patchMotion time index)) (center time)
    let coefficient := ∑ source ∈ Finset.univ.erase index,
      4 * scales.circulation (source.val + 1) / (Real.pi * distance time source ^ 3)
    have receiverIdentity : (4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
        (∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) / distance time source ^ 3) =
        coefficient * (1024 * scales.radius (index.val + 1) ^ 2 * deformation) := by
      dsimp only [coefficient]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro source _
      ring
    rw [receiverIdentity] at errorBound
    have combined : coefficient * radius time * scales.length (index.val + 1) +
        coefficient * (1024 * scales.radius (index.val + 1) ^ 2 * deformation) =
        coefficient * (radius time * scales.length (index.val + 1) +
          1024 * scales.radius (index.val + 1) ^ 2 * deformation) := by ring
    rw [combined] at errorBound
    have refined := errorBound.trans (mul_le_mul_of_nonneg_right (hessianBound time member)
      (add_nonneg (mul_nonneg (radiusPositive time member).le (scales.length_pos _).le)
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) nonnegative)))
    have lipschitz := evolution.externalPatch_biotSavart_lipschitzOn (timeRange member)
      amplitudePositive frequencyPositive ratioPositive index (distance time)
      (Metric.closedBall (center time) (radius time)) (positive time member) (separated time member) (strainBound time member)
    have linearBound := norm_fderiv_le_of_lipschitzOn ℝ
      (Metric.closedBall_mem_nhds (center time) (radiusPositive time member)) lipschitz
    refine ⟨derivative.differentiableAt.hasDerivAt, ?_⟩
    calc
      _ = ‖linear (centroidAsymmetry family.patchMotion time index) +
          (deriv (fun parameter => centroidAsymmetry family.patchMotion parameter index) time -
            linear (centroidAsymmetry family.patchMotion time index))‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add
        ((linear.le_opNorm _).trans (mul_le_mul_of_nonneg_right linearBound (norm_nonneg _))) refined)
  exact norm_integral_gronwall continuous
    (continuous_const.mul ((radiusContinuous.mul continuous_const).add continuous_const))
    strain.property finishNonnegative
    (fun time member => (localEstimate time ⟨member.1, member.2.le⟩).1.hasDerivWithinAt)
    (fun time member => (localEstimate time ⟨member.1, member.2.le⟩).2)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
