import EulerNonuniqueness.Section6.SourcePacketOutgoingCoefficientSeries
import EulerNonuniqueness.Section6.SourcePacketVelocityWeightedBudget
import EulerNonuniqueness.General.WeightedNonnegativeSeriesIntegral

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.SourcePacketPhysicalGeometry

open EulerNonuniqueness.Section6

variable {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count}
  {start horizon chartRadius : ℝ}

set_option maxHeartbeats 1000000

theorem actual_outgoing_coefficient_series_weighted_integral_bound
    (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius)
    (horizonNonnegative : 0 ≤ horizon)
    (radii : ∀ patch, (family.patch (finProdFinEquiv (source, patch))).radius = scales.radius (source.val + 1))
    (centers : ∀ elapsed ∈ Icc 0 horizon, ∀ patch,
      (family.patch (finProdFinEquiv (source, patch))).center (start + elapsed) =
        patchCentroid family.patchMotion (start + elapsed) source patch)
    {receiverRadius distance weight decay : ℝ}
    (receiverNonnegative : 0 ≤ receiverRadius) (positive : 0 < distance)
    (weightNonnegative : 0 ≤ weight) (decayPositive : 0 < decay)
    (gapBound : 2 * distance ≤ geometry.gap) (observationBound : 2 * distance ≤ geometry.observationDistance)
    (small : 4 * weight * receiverRadius / distance < 1)
    (coefficientsContinuous : ∀ power : ℕ, ContinuousOn (fun elapsed =>
      (family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
        (fun time => geometry.location (time - start)) receiverRadius (power + 1) (start + elapsed)) (Icc 0 horizon)) :
    let coefficient := fun power elapsed =>
      (family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
        (fun time => geometry.location (time - start)) receiverRadius (power + 1) (start + elapsed)
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) *
      ∑' power : ℕ, weight ^ (power + 1) * ‖coefficient power elapsed‖) volume 0 horizon ∧
    decay * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
      ∑' power : ℕ, weight ^ (power + 1) * ‖coefficient power elapsed‖) ≤
      (weight * (scales.circulation (source.val + 1) / (2 * Real.pi)) *
        (1 - 4 * weight * receiverRadius / distance)⁻¹) *
        (4 * distance⁻¹ ^ 3 * decay * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
            ‖geometry.firstSeparation elapsed + geometry.secondSeparation elapsed‖) +
          128 * distance⁻¹ ^ 4 * geometry.halfWidth * decay *
            (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
              ‖geometry.firstCenter elapsed - geometry.secondCenter elapsed‖)) +
      (256 * weight * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 *
        distance⁻¹ ^ 4 / Real.pi) * (1 - 4 * weight * receiverRadius / distance)⁻¹ := by
  dsimp only
  let coefficient := fun power elapsed =>
    (family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
      (fun time => geometry.location (time - start)) receiverRadius (power + 1) (start + elapsed)
  let terms := fun power elapsed => weight ^ (power + 1) * ‖coefficient power elapsed‖
  let neutral := fun elapsed => ‖geometry.firstSeparation elapsed + geometry.secondSeparation elapsed‖
  let separation := fun elapsed => ‖geometry.firstCenter elapsed - geometry.secondCenter elapsed‖
  let prefactor := weight * (scales.circulation (source.val + 1) / (2 * Real.pi)) *
    (1 - 4 * weight * receiverRadius / distance)⁻¹
  let neutralCoefficient := prefactor * 4 * distance⁻¹ ^ 3
  let separationCoefficient := prefactor * 128 * distance⁻¹ ^ 4 * geometry.halfWidth
  let correction := (256 * weight * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 *
    distance⁻¹ ^ 4 / Real.pi) * (1 - 4 * weight * receiverRadius / distance)⁻¹
  let majorant := fun elapsed => neutralCoefficient * neutral elapsed + separationCoefficient * separation elapsed + correction
  have circulationPositive := scales.circulation_pos geometry.frequencyPositive geometry.ratioPositive (source.val + 1)
  have correctionNonnegative : 0 ≤ correction := by
    dsimp only [correction]
    exact mul_nonneg (by positivity) (inv_nonneg.mpr (sub_nonneg.mpr small.le))
  have centroidContinuous (patch : Fin 4) :
      Continuous (fun elapsed => patchCentroid family.patchMotion (start + elapsed) source patch) := by
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
  have separationContinuous : Continuous separation := (geometry.firstCenterContinuous.sub geometry.secondCenterContinuous).norm
  have majorantContinuous : ContinuousOn majorant (Icc 0 horizon) :=
    ((continuousOn_const.mul neutralContinuous).add
      (continuousOn_const.mul separationContinuous.continuousOn)).add continuousOn_const
  have exponentialContinuous : Continuous (fun elapsed : ℝ => Real.exp (-decay * elapsed)) := by fun_prop
  have termsContinuous (power : ℕ) : ContinuousOn (terms power) (Icc 0 horizon) :=
    continuousOn_const.mul (coefficientsContinuous power).norm
  have pointwise (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      Summable (fun power : ℕ => terms power elapsed) ∧ (∑' power : ℕ, terms power elapsed) ≤ majorant elapsed := by
    have actual := geometry.actual_outgoing_coefficient_series_summable_and_tsum_le inside radii
      (centers elapsed inside) receiverNonnegative positive weightNonnegative gapBound observationBound small
    refine ⟨actual.1, ?_⟩
    convert actual.2 using 1 <;>
      dsimp only [terms, coefficient, majorant, neutralCoefficient, separationCoefficient, prefactor, neutral, separation, correction] <;> ring
  have integrated := General.intervalIntegrable_weighted_tsum_of_continuousOn_majorant horizonNonnegative termsContinuous
    (fun power _ _ => mul_nonneg (pow_nonneg weightNonnegative (power + 1)) (norm_nonneg _))
    (fun elapsed inside => (pointwise elapsed inside).1) exponentialContinuous.continuousOn
    (fun elapsed _ => (Real.exp_pos (-decay * elapsed)).le) majorantContinuous
    (fun elapsed inside => (pointwise elapsed inside).2)
  have neutralIntegrable := (exponentialContinuous.continuousOn.mul neutralContinuous).intervalIntegrable_of_Icc
    (μ := volume) horizonNonnegative
  have separationIntegrable := (exponentialContinuous.mul separationContinuous).intervalIntegrable (μ := volume) 0 horizon
  have exponentialIntegrable := exponentialContinuous.intervalIntegrable (μ := volume) 0 horizon
  have expansion : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * majorant elapsed) =
      neutralCoefficient * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * neutral elapsed) +
        separationCoefficient * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * separation elapsed) +
        correction * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed)) := by
    dsimp only [majorant]
    simp_rw [mul_add, mul_left_comm (Real.exp _) neutralCoefficient,
      mul_left_comm (Real.exp _) separationCoefficient, mul_comm (Real.exp _) correction]
    rw [intervalIntegral.integral_add
        ((neutralIntegrable.const_mul _).add (separationIntegrable.const_mul _)) (exponentialIntegrable.const_mul correction),
      intervalIntegral.integral_add (neutralIntegrable.const_mul _) (separationIntegrable.const_mul _)]
    simp only [intervalIntegral.integral_const_mul]
  have exponentialBound : decay * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed)) ≤ 1 := by
    have bound := laplace_affine_integral_bound (decay := decay) (slope := 0) (constant := 1)
      decayPositive (by norm_num) (by norm_num) horizonNonnegative
    simp only [zero_mul, zero_add, mul_one, zero_div] at bound
    exact (mul_le_mul_of_nonneg_left bound decayPositive.le).trans_eq (by field_simp [decayPositive.ne'])
  have weighted := mul_le_mul_of_nonneg_left integrated.2 decayPositive.le
  rw [expansion] at weighted
  have errorBound := mul_le_mul_of_nonneg_left exponentialBound correctionNonnegative
  refine ⟨integrated.1, weighted.trans ?_⟩
  have result := add_le_add_left errorBound
    (prefactor * (4 * distance⁻¹ ^ 3 * decay *
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * neutral elapsed) +
      128 * distance⁻¹ ^ 4 * geometry.halfWidth * decay *
        (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * separation elapsed)))
  convert result using 1 <;> dsimp only [neutralCoefficient, separationCoefficient, prefactor, correction, neutral, separation] <;> ring

end EulerNonuniqueness.Paper.SourcePacketPhysicalGeometry
