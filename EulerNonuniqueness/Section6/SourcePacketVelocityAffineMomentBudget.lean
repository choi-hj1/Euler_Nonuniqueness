import EulerNonuniqueness.Section6.SourcePacketVelocityWeightedBudget
import EulerNonuniqueness.Section6.MovingPairedWindowMemory

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Paper.SourcePacketPhysicalGeometry

open EulerNonuniqueness.Section6

theorem actual_velocity_affine_moment_budget
    {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count}
    {start horizon chartRadius : ℝ}
    (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius)
    (horizonNonnegative : 0 ≤ horizon) {weight hessian radius slope intercept : ℝ} {strain : ℝ≥0}
    (hessianNonnegative : 0 ≤ hessian) (decayGap : 0 < weight - (strain : ℝ))
    (finalTimePositive : 0 < geometry.finalTime)
    (interior : ∀ elapsed ∈ Icc 0 horizon, ∀ index,
      start + elapsed ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ elapsed ∈ Icc 0 horizon, ∀ index label,
      (family.patch index).boundaryVelocity (start + elapsed) label =
        biotSavart (family.vorticity (start + elapsed)) ((family.patch index).boundary (start + elapsed) label))
    (center : ℝ → ℂ) (radiusPositive : 0 < radius)
    (distance : ℝ → Fin count → ℝ)
    (positive : ∀ elapsed ∈ Icc 0 horizon, ∀ other ∈ Finset.univ.erase source, 0 < distance elapsed other)
    (separated : ∀ elapsed ∈ Icc 0 horizon, ∀ position ∈ Metric.closedBall (center elapsed) radius,
      ∀ other ∈ Finset.univ.erase source, ∀ patch,
      ∀ location ∈ family.patchMotion.domain (start + elapsed) other patch, distance elapsed other ≤ ‖position - location‖)
    (centroidsInside : ∀ elapsed ∈ Icc 0 horizon, ∀ patch,
      patchCentroid family.patchMotion (start + elapsed) source patch ∈ Metric.closedBall (center elapsed) radius)
    (widthSmall : geometry.halfWidth ≤ scales.length (source.val + 1))
    (sourceBounded : ∀ elapsed ∈ Icc 0 horizon, ∀ other ∈ Finset.univ.erase source, ∀ patch,
      family.patchMotion.domain (start + elapsed) other patch ⊆ Metric.closedBall
        (patchCentroid family.patchMotion (start + elapsed) other patch) (2 * scales.radius (other.val + 1)))
    (receiverSmall : ∀ elapsed ∈ Icc 0 horizon, ∀ other ∈ Finset.univ.erase source,
      8 * scales.radius (source.val + 1) ≤ distance elapsed other)
    (sourceSmall : ∀ elapsed ∈ Icc 0 horizon, ∀ other ∈ Finset.univ.erase source,
      4 * scales.radius (other.val + 1) ≤ distance elapsed other)
    (centroidsSeparated : ∀ elapsed ∈ Icc 0 horizon, ∀ receiver,
      ∀ other ∈ Finset.univ.erase source, ∀ patch,
      distance elapsed other ≤ ‖patchCentroid family.patchMotion (start + elapsed) source receiver -
        patchCentroid family.patchMotion (start + elapsed) other patch‖)
    (strainBound : ∀ elapsed ∈ Icc 0 horizon,
      (∑ other ∈ Finset.univ.erase source,
        2 * scales.circulation (other.val + 1) / (Real.pi * distance elapsed other ^ 2)) ≤ (strain : ℝ))
    (hessianBound : ∀ elapsed ∈ Icc 0 horizon,
      (∑ other ∈ Finset.univ.erase source,
        4 * scales.circulation (other.val + 1) / (Real.pi * distance elapsed other ^ 3)) ≤ hessian)
    (slopeNonnegative : 0 ≤ slope) (interceptNonnegative : 0 ≤ intercept)
    (outgoingAffine : ∀ elapsed ∈ Icc 0 horizon,
      ‖geometry.firstCenter elapsed - geometry.secondCenter elapsed‖ ≤ slope * elapsed + intercept) :
    IntervalIntegrable (fun elapsed => Real.exp (-weight * elapsed) *
      ‖biotSavart (quadrupoleDensity scales family.patchMotion (start + elapsed) source) (geometry.location elapsed)‖)
      volume 0 horizon ∧
    weight * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) *
      ‖biotSavart (quadrupoleDensity scales family.patchMotion (start + elapsed) source) (geometry.location elapsed)‖) ≤
      (40 * scales.circulation (source.val + 1) / (2 * Real.pi)) *
        (4 * weight * (hessian * (radius * scales.length (source.val + 1) +
            1024 * scales.radius (source.val + 1) ^ 2 * geometry.deformation) / (weight - (strain : ℝ)) ^ 2 +
            ‖centroidAsymmetry family.patchMotion start source‖ / (weight - (strain : ℝ))) /
          geometry.observationDistance ^ 2 +
          geometry.halfWidth * (slope / weight + intercept) / geometry.observationDistance ^ 3) +
        32 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 / (Real.pi * geometry.gap ^ 3) := by
  have weightPositive : 0 < weight := by linarith [strain.coe_nonneg]
  have coordinates (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      ‖patchCentroid family.patchMotion (start + elapsed) source 0 -
          patchCentroid family.patchMotion (start + elapsed) source 3‖ ≤ 2 * scales.length (source.val + 1) ∧
      ‖patchCentroid family.patchMotion (start + elapsed) source 1 -
          patchCentroid family.patchMotion (start + elapsed) source 2‖ ≤ 2 * scales.length (source.val + 1) ∧
      ‖geometry.firstSeparation elapsed + geometry.secondSeparation elapsed‖ =
        4 * ‖centroidAsymmetry family.patchMotion (start + elapsed) source‖ := by
    have first := congrFun (geometry.positions elapsed inside) 0
    have second := congrFun (geometry.positions elapsed inside) 1
    have third := congrFun (geometry.positions elapsed inside) 2
    have fourth := congrFun (geometry.positions elapsed inside) 3
    simp [relabelNegativePoints, negativeLabelSwap, Equiv.swap_apply_def, twoDipoleConfiguration] at first second third fourth
    have firstIdentity : patchCentroid family.patchMotion (start + elapsed) source 0 -
        patchCentroid family.patchMotion (start + elapsed) source 3 = geometry.firstSeparation elapsed := by rw [first, third]; ring
    have secondIdentity : patchCentroid family.patchMotion (start + elapsed) source 1 -
        patchCentroid family.patchMotion (start + elapsed) source 2 = geometry.secondSeparation elapsed := by rw [second, fourth]; ring
    refine ⟨?_, ?_, ?_⟩
    · rw [firstIdentity]
      exact (geometry.firstBound elapsed inside).trans (by linarith)
    · rw [secondIdentity]
      exact (geometry.secondBound elapsed inside).trans (by linarith)
    · have identity : geometry.firstSeparation elapsed + geometry.secondSeparation elapsed =
          4 * centroidAsymmetry family.patchMotion (start + elapsed) source := by
        dsimp only [centroidAsymmetry]
        rw [first, second, fourth, third]
        ring
      rw [identity, norm_mul]
      norm_num
  have memory := family.centroidAsymmetry_paired_window_weighted_bound scales geometry.densities
    horizonNonnegative hessianNonnegative decayGap geometry.evolution finalTimePositive geometry.timeRange
    geometry.amplitudePositive geometry.frequencyPositive geometry.ratioPositive interior material source center radiusPositive
    distance positive separated centroidsInside (fun elapsed inside => (coordinates elapsed inside).1)
    (fun elapsed inside => (coordinates elapsed inside).2.1) geometry.control geometry.deformationNonnegative geometry.deformationSmall
    sourceBounded receiverSmall sourceSmall centroidsSeparated strainBound hessianBound
  have neutralIntegral : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) *
      ‖geometry.firstSeparation elapsed + geometry.secondSeparation elapsed‖) =
      4 * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) *
        ‖centroidAsymmetry family.patchMotion (start + elapsed) source‖) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro elapsed inside
    dsimp only
    rw [(coordinates elapsed (by simpa only [uIcc_of_le horizonNonnegative] using inside)).2.2]
    ring
  have distanceContinuous := (geometry.firstCenterContinuous.sub geometry.secondCenterContinuous).norm
  have affineContinuous : Continuous (fun elapsed : ℝ => Real.exp (-weight * elapsed) * (slope * elapsed + intercept)) := by fun_prop
  have distanceIntegral := intervalIntegral.integral_mono_on (μ := volume) horizonNonnegative
    (((by fun_prop : Continuous (fun elapsed : ℝ => Real.exp (-weight * elapsed))).mul distanceContinuous).intervalIntegrable 0 horizon)
    (affineContinuous.intervalIntegrable 0 horizon)
    (fun elapsed inside => mul_le_mul_of_nonneg_left (outgoingAffine elapsed inside) (Real.exp_pos _).le)
  have distanceBound := distanceIntegral.trans (laplace_affine_integral_bound weightPositive slopeNonnegative interceptNonnegative horizonNonnegative)
  have weightedDistance := mul_le_mul_of_nonneg_left distanceBound weightPositive.le
  have weightedDistanceBound : weight * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) *
      ‖geometry.firstCenter elapsed - geometry.secondCenter elapsed‖) ≤ slope / weight + intercept := by
    convert weightedDistance using 1
    field_simp [weightPositive.ne']
    ring
  obtain ⟨integrable, actual⟩ := geometry.actual_velocity_weighted_integral_bound horizonNonnegative weightPositive
  refine ⟨integrable, actual.trans ?_⟩
  rw [neutralIntegral]
  have circulationNonnegative := (scales.circulation_pos geometry.frequencyPositive geometry.ratioPositive (source.val + 1)).le
  have observationPositive := geometry.observationPositive
  have neutralBound := mul_le_mul_of_nonneg_left memory (show 0 ≤ 4 * weight by positivity)
  have neutralNormalized := div_le_div_of_nonneg_right neutralBound (sq_nonneg geometry.observationDistance)
  have distanceNormalized := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left weightedDistanceBound geometry.widthPositive.le)
    (pow_nonneg observationPositive.le 3)
  have combined := add_le_add neutralNormalized distanceNormalized
  have scaled := mul_le_mul_of_nonneg_left combined
    (show 0 ≤ 40 * scales.circulation (source.val + 1) / (2 * Real.pi) by positivity)
  have result := add_le_add_right scaled
    (32 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 / (Real.pi * geometry.gap ^ 3))
  convert result using 1 <;> ring

end EulerNonuniqueness.Paper.SourcePacketPhysicalGeometry
