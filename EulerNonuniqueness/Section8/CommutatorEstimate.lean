import EulerNonuniqueness.Section8.CommutatorCancellation
import EulerNonuniqueness.Section8.TranslationEstimate
import EulerNonuniqueness.General.TranslationLp
import EulerNonuniqueness.General.L2Products

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

def scaledCenteredTransportIntegrand (kernel : Plane → ℝ) (velocity : Velocity)
    (vorticity : Vorticity) (scale : ℝ) (offset position : Plane) : ℝ :=
  (vorticity (position - scale • offset) - vorticity position) * fderiv ℝ kernel offset
    (scale⁻¹ • (velocity position - velocity (position - scale • offset)))

theorem integral_scaledCenteredTransportIntegrand_norm_le {vorticity : Vorticity} {radius : ℝ}
    (radiusNonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (zeroMean : (∫ position, vorticity position) = 0)
    (kernel : Plane → ℝ) (scale : ℝ) (offset : Plane) :
    Integrable (scaledCenteredTransportIntegrand kernel (biotSavart vorticity) vorticity scale offset) ∧
      (∫ position, ‖scaledCenteredTransportIntegrand kernel (biotSavart vorticity) vorticity scale offset position‖) ≤
        ‖fderiv ℝ kernel offset‖ * ‖offset‖ * (eLpNorm vorticity 2 volume).toReal *
          (eLpNorm (fun position => vorticity (position - scale • offset) - vorticity position) 2 volume).toReal := by
  by_cases scaleZero : scale = 0
  · subst scale
    have zeroFunction : scaledCenteredTransportIntegrand kernel (biotSavart vorticity) vorticity 0 offset =
        (0 : Plane → ℝ) := funext fun position => by simp [scaledCenteredTransportIntegrand]
    rw [zeroFunction]
    constructor
    · exact integrable_zero Plane ℝ volume
    · simp
  have integrable : Integrable vorticity :=
    memLp_one_iff_integrable.mp (by simpa using membership 1 le_rfl)
  have sourceMember : MemLp vorticity 2 volume := by simpa using membership 2 (by norm_num)
  have velocityMember : MemLp (biotSavart vorticity) 2 volume :=
    memLp_biotSavart_two_of_memLp_support_integral_zero holderConjugate_four_fourThirds
      (membership 4 (by norm_num)) (by norm_num) integrable zeroMean radiusNonnegative supportBound
  let sourceDifference := fun position => vorticity (position - scale • offset) - vorticity position
  let velocityDifference := fun position => biotSavart vorticity position - biotSavart vorticity (position - scale • offset)
  have sourceDifferenceMember : MemLp sourceDifference 2 volume :=
    (sourceMember.comp_measurePreserving (translationMeasurePreserving (scale • offset))).sub sourceMember
  have velocityDifferenceMember : MemLp velocityDifference 2 volume :=
    velocityMember.sub (velocityMember.comp_measurePreserving (translationMeasurePreserving (scale • offset)))
  have productIntegrable : Integrable (fun position => sourceDifference position • (scale⁻¹ • velocityDifference position)) :=
    memLp_one_iff_integrable.mp ((velocityDifferenceMember.const_smul scale⁻¹).smul sourceDifferenceMember)
  have commutatorIntegrable : Integrable
      (scaledCenteredTransportIntegrand kernel (biotSavart vorticity) vorticity scale offset) := by
    change Integrable (fun position => sourceDifference position *
      fderiv ℝ kernel offset (scale⁻¹ • velocityDifference position))
    simpa only [map_smul, smul_eq_mul] using
      (fderiv ℝ kernel offset).integrable_comp productIntegrable
  refine ⟨commutatorIntegrable, ?_⟩
  have velocityNormEquality : eLpNorm velocityDifference 2 volume =
      eLpNorm (fun position => biotSavart vorticity (position + -(scale • offset)) - biotSavart vorticity position) 2 volume := by
    apply eLpNorm_congr_norm_ae
    exact Filter.Eventually.of_forall fun position => by
      dsimp only [velocityDifference]
      rw [← sub_eq_add_neg]
      exact norm_sub_rev _ _
  have velocityBound : (eLpNorm velocityDifference 2 volume).toReal ≤
      |scale| * ‖offset‖ * (eLpNorm vorticity 2 volume).toReal := by
    rw [velocityNormEquality]
    have inequality := eLpNorm_translation_biotSavart_le radiusNonnegative membership supportBound zeroMean (-(scale • offset))
    have realInequality := ENNReal.toReal_mono (by simp) inequality
    simp only [norm_neg, norm_smul, Real.norm_eq_abs] at realInequality
    rw [ENNReal.toReal_ofReal (by positivity)] at realInequality
    exact realInequality
  let coefficient := ‖fderiv ℝ kernel offset‖ * |scale|⁻¹
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp [coefficient]; positivity
  have pointwise : ∀ position : Plane,
      ‖scaledCenteredTransportIntegrand kernel (biotSavart vorticity) vorticity scale offset position‖ ≤
        coefficient * (‖sourceDifference position‖ * ‖velocityDifference position‖) := by
    intro position
    change ‖sourceDifference position * (fderiv ℝ kernel offset) (scale⁻¹ • velocityDifference position)‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ ‖sourceDifference position‖ *
          (‖fderiv ℝ kernel offset‖ * ‖scale⁻¹ • velocityDifference position‖) :=
        mul_le_mul_of_nonneg_left ((fderiv ℝ kernel offset).le_opNorm _) (norm_nonneg _)
      _ = _ := by simp only [norm_smul, norm_inv, Real.norm_eq_abs]; dsimp [coefficient]; ring
  have productNormIntegrable : Integrable (fun position => ‖sourceDifference position‖ * ‖velocityDifference position‖) :=
    sourceDifferenceMember.norm.integrable_mul velocityDifferenceMember.norm
  have integralBound := integral_mono commutatorIntegrable.norm (productNormIntegrable.const_mul coefficient) pointwise
  rw [integral_const_mul] at integralBound
  calc
    _ ≤ coefficient * (∫ position, ‖sourceDifference position‖ * ‖velocityDifference position‖) := integralBound
    _ ≤ coefficient * ((eLpNorm sourceDifference 2 volume).toReal * (eLpNorm velocityDifference 2 volume).toReal) :=
      mul_le_mul_of_nonneg_left
        (integral_norm_mul_norm_le_eLpNorm_two sourceDifferenceMember velocityDifferenceMember) coefficientNonnegative
    _ ≤ coefficient * ((eLpNorm sourceDifference 2 volume).toReal *
        (|scale| * ‖offset‖ * (eLpNorm vorticity 2 volume).toReal)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left velocityBound ENNReal.toReal_nonneg) coefficientNonnegative
    _ = _ := by
      dsimp only [coefficient, sourceDifference]
      field_simp [abs_ne_zero.mpr scaleZero]
      ring

end EulerNonuniqueness
