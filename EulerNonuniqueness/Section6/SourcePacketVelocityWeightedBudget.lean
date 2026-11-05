import EulerNonuniqueness.Section6.SourcePacketVelocityPhysicalBound
import EulerNonuniqueness.Section3.MovingMaterialCentroidRegularity
import EulerNonuniqueness.Section6.LaplaceMomentErrorBound

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

local instance velocityWeightedHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance velocityWeightedC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

open EulerNonuniqueness.Section6

theorem MovingMaterialPatch.centroid_continuous_global (path : MovingMaterialPatch) : Continuous path.centroid := by
  have shapeCentroid : Continuous (fun time => contourCentroidFunctional (path.shape time)) := by
    apply continuous_iff_continuousAt.mpr
    intro time
    exact (analyticAt_contourCentroidFunctional (path.shape time) (path.nearby time)).continuousAt.comp
      path.shape_continuous.continuousAt
  have rotation : Continuous (fun time => (Circle.exp (path.phase time) : ℂ)) := by
    simp only [Circle.coe_exp]
    exact ((Complex.continuous_ofReal.comp path.phase_continuous).mul continuous_const).cexp
  have actual := path.center_continuous.add ((rotation.mul shapeCentroid).const_smul path.radius)
  exact actual.congr fun time => (path.centroid_eq_center_add_contourCentroid time).symm

namespace SourcePacketPhysicalGeometry

variable {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count}
  {start horizon chartRadius : ℝ}

theorem actual_velocity_weighted_integral_bound
    (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius)
    (horizonNonnegative : 0 ≤ horizon) {weight : ℝ} (weightPositive : 0 < weight) :
    IntervalIntegrable (fun elapsed => Real.exp (-weight * elapsed) *
      ‖biotSavart (quadrupoleDensity scales family.patchMotion (start + elapsed) source) (geometry.location elapsed)‖)
      volume 0 horizon ∧
    weight * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) *
      ‖biotSavart (quadrupoleDensity scales family.patchMotion (start + elapsed) source) (geometry.location elapsed)‖) ≤
      (40 * scales.circulation (source.val + 1) / (2 * Real.pi)) *
        (weight * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) *
          ‖geometry.firstSeparation elapsed + geometry.secondSeparation elapsed‖) / geometry.observationDistance ^ 2 +
          geometry.halfWidth * weight * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) *
            ‖geometry.firstCenter elapsed - geometry.secondCenter elapsed‖) / geometry.observationDistance ^ 3) +
        32 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 / (Real.pi * geometry.gap ^ 3) := by
  let neutral := fun elapsed => ‖geometry.firstSeparation elapsed + geometry.secondSeparation elapsed‖
  let distance := fun elapsed => ‖geometry.firstCenter elapsed - geometry.secondCenter elapsed‖
  let velocity := fun elapsed => ‖biotSavart (quadrupoleDensity scales family.patchMotion (start + elapsed) source) (geometry.location elapsed)‖
  let coefficient := 40 * scales.circulation (source.val + 1) / (2 * Real.pi)
  let correction := 32 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 / (Real.pi * geometry.gap ^ 3)
  let majorant := fun elapsed => coefficient / geometry.observationDistance ^ 2 * neutral elapsed +
    coefficient * geometry.halfWidth / geometry.observationDistance ^ 3 * distance elapsed + correction
  have circulationPositive := scales.circulation_pos geometry.frequencyPositive geometry.ratioPositive (source.val + 1)
  have observationPositive := geometry.observationPositive
  have gapPositive := geometry.gapPositive
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have correctionNonnegative : 0 ≤ correction := by dsimp only [correction]; positivity
  have centroidContinuous (patch : Fin 4) : Continuous (fun elapsed => patchCentroid family.patchMotion (start + elapsed) source patch) := by
    simp_rw [FiniteMovingPatchFamily.patchCentroid_eq]
    exact (family.patch _).centroid_continuous_global.comp (continuous_const.add continuous_id)
  have signedContinuous : Continuous (fun elapsed => fourPointSignedMoment
      (relabelNegativePoints (fun patch => patchCentroid family.patchMotion (start + elapsed) source patch))) :=
    continuous_finset_sum _ (fun patch _ => continuous_const.mul (centroidContinuous (negativeLabelSwap patch)))
  have neutralContinuous : ContinuousOn neutral (Icc 0 horizon) := by
    apply signedContinuous.norm.continuousOn.congr
    intro elapsed inside
    dsimp only [neutral]
    rw [geometry.positions elapsed inside, twoDipole_signed_moment]
  have distanceContinuous : Continuous distance := (geometry.firstCenterContinuous.sub geometry.secondCenterContinuous).norm
  have majorantContinuous : ContinuousOn majorant (Icc 0 horizon) :=
    ((continuousOn_const.mul neutralContinuous).add (continuousOn_const.mul distanceContinuous.continuousOn)).add continuousOn_const
  have exponentialContinuous : Continuous (fun elapsed : ℝ => Real.exp (-weight * elapsed)) := by fun_prop
  have majorantIntegrable := (exponentialContinuous.continuousOn.mul majorantContinuous).intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have neutralIntegrable := (exponentialContinuous.continuousOn.mul neutralContinuous).intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have distanceIntegrable := (exponentialContinuous.mul distanceContinuous).intervalIntegrable (μ := volume) 0 horizon
  have exponentialIntegrable := exponentialContinuous.intervalIntegrable (μ := volume) 0 horizon
  have velocityMeasurable : Measurable velocity := by
    have joint := measurable_biotSavart_of_measurable_vorticity (Parameter := ℝ)
      (vorticity := fun time => quadrupoleDensity scales family.patchMotion time source)
      (family.measurable_quadrupoleDensity scales geometry.densities source)
    exact (joint.comp ((measurable_const.add measurable_id).prodMk geometry.locationContinuous.measurable)).norm
  have pointwise (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : velocity elapsed ≤ majorant elapsed := by
    have actual := geometry.actual_velocity_far_field_bound inside
    have lower := geometry.observationLower elapsed inside
    have firstTerm := div_le_div_of_nonneg_left (norm_nonneg (geometry.firstSeparation elapsed + geometry.secondSeparation elapsed))
      (sq_pos_of_pos observationPositive) (pow_le_pow_left₀ observationPositive.le lower 2)
    have secondTerm := div_le_div_of_nonneg_left
      (mul_nonneg geometry.widthPositive.le (norm_nonneg (geometry.firstCenter elapsed - geometry.secondCenter elapsed)))
      (pow_pos observationPositive 3) (pow_le_pow_left₀ observationPositive.le lower 3)
    apply actual.trans
    have comparison := add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add firstTerm secondTerm) coefficientNonnegative) correction
    convert comparison using 1 <;> dsimp only [coefficient, correction, majorant, neutral, distance] <;> ring
  have actualIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-weight * elapsed) * velocity elapsed) volume 0 horizon :=
    majorantIntegrable.mono_fun' (exponentialContinuous.measurable.mul velocityMeasurable).aestronglyMeasurable.restrict (by
      rw [uIoc_of_le horizonNonnegative]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with elapsed inside
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (pointwise elapsed ⟨inside.1.le, inside.2⟩) (Real.exp_pos _).le)
  refine ⟨actualIntegrable, ?_⟩
  have comparison := intervalIntegral.integral_mono_on (μ := volume) horizonNonnegative actualIntegrable majorantIntegrable
    (fun elapsed inside => mul_le_mul_of_nonneg_left (pointwise elapsed inside) (Real.exp_pos _).le)
  have expansion : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * majorant elapsed) =
      coefficient / geometry.observationDistance ^ 2 * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * neutral elapsed) +
        coefficient * geometry.halfWidth / geometry.observationDistance ^ 3 *
          (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * distance elapsed) +
        correction * ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) := by
    dsimp only [majorant]
    simp_rw [mul_add, mul_left_comm (Real.exp _) (coefficient / geometry.observationDistance ^ 2),
      mul_left_comm (Real.exp _) (coefficient * geometry.halfWidth / geometry.observationDistance ^ 3),
      mul_comm (Real.exp _) correction]
    rw [intervalIntegral.integral_add
        ((neutralIntegrable.const_mul _).add (distanceIntegrable.const_mul _)) (exponentialIntegrable.const_mul correction),
      intervalIntegral.integral_add (neutralIntegrable.const_mul _) (distanceIntegrable.const_mul _)]
    simp only [intervalIntegral.integral_const_mul]
  rw [expansion] at comparison
  have exponentialBound : weight * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed)) ≤ 1 := by
    have bound := laplace_affine_integral_bound (decay := weight) (slope := 0) (constant := 1)
      weightPositive (by norm_num) (by norm_num) horizonNonnegative
    simp only [zero_mul, zero_add, mul_one, zero_div] at bound
    exact (mul_le_mul_of_nonneg_left bound weightPositive.le).trans_eq (by field_simp [weightPositive.ne'])
  have weighted := mul_le_mul_of_nonneg_left comparison weightPositive.le
  have errorBound := mul_le_mul_of_nonneg_left exponentialBound correctionNonnegative
  change weight * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * velocity elapsed) ≤ _
  calc
    _ ≤ weight * (coefficient / geometry.observationDistance ^ 2 *
        (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * neutral elapsed) +
        coefficient * geometry.halfWidth / geometry.observationDistance ^ 3 *
          (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * distance elapsed) +
        correction * ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed)) := weighted
    _ ≤ coefficient * (weight * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * neutral elapsed) /
        geometry.observationDistance ^ 2 + geometry.halfWidth * weight *
        (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * distance elapsed) / geometry.observationDistance ^ 3) + correction := by
      have result := add_le_add_left errorBound
        (coefficient * (weight * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * neutral elapsed) /
          geometry.observationDistance ^ 2 + geometry.halfWidth * weight *
          (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * distance elapsed) / geometry.observationDistance ^ 3))
      convert result using 1 <;> ring
    _ = _ := by rfl

end SourcePacketPhysicalGeometry
end EulerNonuniqueness.Paper
