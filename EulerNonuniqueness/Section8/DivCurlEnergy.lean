import EulerNonuniqueness.Section8.Curl
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem contDiff_directionalDerivative {function : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ function) (direction : Plane) :
    ContDiff ℝ ∞ (fun position => fderiv ℝ function position direction) :=
  (smooth.fderiv_right (by simp)).clm_apply contDiff_const

theorem mixed_directionalDerivatives_commute {function : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ function) (first second position : Plane) :
    fderiv ℝ (fun point => fderiv ℝ function point first) position second =
      fderiv ℝ (fun point => fderiv ℝ function point second) position first := by
  have differentiableDerivative : Differentiable ℝ (fderiv ℝ function) :=
    (smooth.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  simp only [fderiv_clm_apply (differentiableDerivative position) (differentiableAt_const _),
    fderiv_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  exact smooth.contDiffAt.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2) second first

theorem integral_cross_directionalDerivatives {first second : Plane → ℝ}
    (firstSmooth : ContDiff ℝ ∞ first) (firstCompact : HasCompactSupport first)
    (secondSmooth : ContDiff ℝ ∞ second)
    (firstDirection secondDirection : Plane) :
    (∫ position, fderiv ℝ first position firstDirection *
      fderiv ℝ second position secondDirection) =
      ∫ position, fderiv ℝ first position secondDirection *
        fderiv ℝ second position firstDirection := by
  have integrationByParts (direction other : Plane) :
      (∫ position, fderiv ℝ first position direction * fderiv ℝ second position other) =
        -(∫ position, first position *
          fderiv ℝ (fun point => fderiv ℝ second point other) position direction) := by
    have firstDerivativeSmooth := contDiff_directionalDerivative firstSmooth direction
    have secondDerivativeSmooth := contDiff_directionalDerivative secondSmooth other
    have secondSecondDerivativeSmooth :=
      contDiff_directionalDerivative secondDerivativeSmooth direction
    have identity := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      ((firstDerivativeSmooth.continuous.mul secondDerivativeSmooth.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.mul_right (firstCompact.fderiv_apply ℝ direction)))
      ((firstSmooth.continuous.mul secondSecondDerivativeSmooth.continuous).integrable_of_hasCompactSupport
        firstCompact.mul_right)
      ((firstSmooth.continuous.mul secondDerivativeSmooth.continuous).integrable_of_hasCompactSupport
        firstCompact.mul_right)
      (firstSmooth.differentiable (by simp)) (secondDerivativeSmooth.differentiable (by simp))
    linarith only [identity]
  rw [integrationByParts, integrationByParts]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun position => by
    dsimp only
    rw [mixed_directionalDerivatives_commute secondSmooth]

theorem integral_divCurl_algebra {firstFirst firstSecond secondFirst secondSecond : Plane → ℝ}
    (firstFirstContinuous : Continuous firstFirst) (firstFirstCompact : HasCompactSupport firstFirst)
    (firstSecondContinuous : Continuous firstSecond) (firstSecondCompact : HasCompactSupport firstSecond)
    (secondFirstContinuous : Continuous secondFirst) (secondFirstCompact : HasCompactSupport secondFirst)
    (secondSecondContinuous : Continuous secondSecond) (secondSecondCompact : HasCompactSupport secondSecond)
    (cross : (∫ position, firstFirst position * secondSecond position) =
      ∫ position, firstSecond position * secondFirst position) :
    (∫ position, firstFirst position ^ 2 + firstSecond position ^ 2 +
      secondFirst position ^ 2 + secondSecond position ^ 2) =
      ∫ position, (firstFirst position + secondSecond position) ^ 2 +
        (secondFirst position - firstSecond position) ^ 2 := by
  have squareIntegrable {function : Plane → ℝ} (continuous : Continuous function)
      (compact : HasCompactSupport function) : Integrable (fun position => function position ^ 2) :=
    (continuous.pow 2).integrable_of_hasCompactSupport
      (compact.comp_left (g := fun value : ℝ => value ^ 2) (by simp))
  have gradientIntegrable :=
    (((squareIntegrable firstFirstContinuous firstFirstCompact).add
      (squareIntegrable firstSecondContinuous firstSecondCompact)).add
      (squareIntegrable secondFirstContinuous secondFirstCompact)).add
      (squareIntegrable secondSecondContinuous secondSecondCompact)
  have firstCrossIntegrable : Integrable (fun position => firstFirst position * secondSecond position) :=
    (firstFirstContinuous.mul secondSecondContinuous).integrable_of_hasCompactSupport
      firstFirstCompact.mul_right
  have secondCrossIntegrable : Integrable (fun position => firstSecond position * secondFirst position) :=
    (firstSecondContinuous.mul secondFirstContinuous).integrable_of_hasCompactSupport
      firstSecondCompact.mul_right
  change Integrable (fun position => firstFirst position ^ 2 + firstSecond position ^ 2 +
    secondFirst position ^ 2 + secondSecond position ^ 2) at gradientIntegrable
  have errorIntegrable : Integrable (fun position =>
      2 * (firstFirst position * secondSecond position - firstSecond position * secondFirst position)) :=
    (firstCrossIntegrable.sub secondCrossIntegrable).const_mul 2
  symm
  calc
    _ = ∫ position, (firstFirst position ^ 2 + firstSecond position ^ 2 +
        secondFirst position ^ 2 + secondSecond position ^ 2) +
        2 * (firstFirst position * secondSecond position -
          firstSecond position * secondFirst position) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun position => by ring
    _ = _ := by
      rw [integral_add gradientIntegrable errorIntegrable,
        integral_const_mul, integral_sub firstCrossIntegrable secondCrossIntegrable, cross]
      ring

theorem integral_divCurl_energy_compact {first second : Plane → ℝ}
    (firstSmooth : ContDiff ℝ ∞ first) (firstCompact : HasCompactSupport first)
    (secondSmooth : ContDiff ℝ ∞ second) (secondCompact : HasCompactSupport second) :
    (∫ position, (fderiv ℝ first position 1) ^ 2 +
      (fderiv ℝ first position Complex.I) ^ 2 +
      (fderiv ℝ second position 1) ^ 2 +
      (fderiv ℝ second position Complex.I) ^ 2) =
      ∫ position, (fderiv ℝ first position 1 + fderiv ℝ second position Complex.I) ^ 2 +
        (fderiv ℝ second position 1 - fderiv ℝ first position Complex.I) ^ 2 := by
  exact integral_divCurl_algebra
    (contDiff_directionalDerivative firstSmooth 1).continuous (firstCompact.fderiv_apply ℝ 1)
    (contDiff_directionalDerivative firstSmooth Complex.I).continuous
      (firstCompact.fderiv_apply ℝ Complex.I)
    (contDiff_directionalDerivative secondSmooth 1).continuous (secondCompact.fderiv_apply ℝ 1)
    (contDiff_directionalDerivative secondSmooth Complex.I).continuous
      (secondCompact.fderiv_apply ℝ Complex.I)
    (integral_cross_directionalDerivatives firstSmooth firstCompact
      secondSmooth 1 Complex.I)

theorem integral_cross_directionalDerivatives_of_memLp {first second : Plane → ℝ}
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second)
    (firstL2 : MemLp first 2 volume)
    (firstDerivativesL2 : ∀ direction : Plane,
      MemLp (fun position => fderiv ℝ first position direction) 2 volume)
    (secondDerivativesL2 : ∀ direction : Plane,
      MemLp (fun position => fderiv ℝ second position direction) 2 volume)
    (secondSecondDerivativesL2 : ∀ firstDirection secondDirection : Plane,
      MemLp (fun position => fderiv ℝ (fun point => fderiv ℝ second point firstDirection)
        position secondDirection) 2 volume)
    (firstDirection secondDirection : Plane) :
    (∫ position, fderiv ℝ first position firstDirection *
      fderiv ℝ second position secondDirection) =
      ∫ position, fderiv ℝ first position secondDirection *
        fderiv ℝ second position firstDirection := by
  have integrationByParts (direction other : Plane) :
      (∫ position, fderiv ℝ first position direction * fderiv ℝ second position other) =
        -(∫ position, first position *
          fderiv ℝ (fun point => fderiv ℝ second point other) position direction) := by
    have secondDerivativeSmooth := contDiff_directionalDerivative secondSmooth other
    have identity := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      ((firstDerivativesL2 direction).integrable_mul (secondDerivativesL2 other))
      (firstL2.integrable_mul (secondSecondDerivativesL2 other direction))
      (firstL2.integrable_mul (secondDerivativesL2 other))
      (firstSmooth.differentiable (by simp)) (secondDerivativeSmooth.differentiable (by simp))
    linarith only [identity]
  rw [integrationByParts, integrationByParts]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun position => by
    dsimp only
    rw [mixed_directionalDerivatives_commute secondSmooth]

theorem integral_divCurl_algebra_of_memLp
    {firstFirst firstSecond secondFirst secondSecond : Plane → ℝ}
    (firstFirstL2 : MemLp firstFirst 2 volume) (firstSecondL2 : MemLp firstSecond 2 volume)
    (secondFirstL2 : MemLp secondFirst 2 volume) (secondSecondL2 : MemLp secondSecond 2 volume)
    (cross : (∫ position, firstFirst position * secondSecond position) =
      ∫ position, firstSecond position * secondFirst position) :
    (∫ position, firstFirst position ^ 2 + firstSecond position ^ 2 +
      secondFirst position ^ 2 + secondSecond position ^ 2) =
      ∫ position, (firstFirst position + secondSecond position) ^ 2 +
        (secondFirst position - firstSecond position) ^ 2 := by
  have squareIntegrable {function : Plane → ℝ} (membership : MemLp function 2 volume) :
      Integrable (fun position => function position ^ 2) :=
    (memLp_two_iff_integrable_sq membership.aestronglyMeasurable).mp membership
  have gradientIntegrable : Integrable (fun position => firstFirst position ^ 2 +
      firstSecond position ^ 2 + secondFirst position ^ 2 + secondSecond position ^ 2) :=
    (((squareIntegrable firstFirstL2).add (squareIntegrable firstSecondL2)).add
      (squareIntegrable secondFirstL2)).add (squareIntegrable secondSecondL2)
  have firstCrossIntegrable : Integrable (fun position => firstFirst position * secondSecond position) :=
    firstFirstL2.integrable_mul secondSecondL2
  have secondCrossIntegrable : Integrable (fun position => firstSecond position * secondFirst position) :=
    firstSecondL2.integrable_mul secondFirstL2
  have errorIntegrable : Integrable (fun position =>
      2 * (firstFirst position * secondSecond position - firstSecond position * secondFirst position)) :=
    (firstCrossIntegrable.sub secondCrossIntegrable).const_mul 2
  symm
  calc
    _ = ∫ position, (firstFirst position ^ 2 + firstSecond position ^ 2 +
        secondFirst position ^ 2 + secondSecond position ^ 2) +
        2 * (firstFirst position * secondSecond position -
          firstSecond position * secondFirst position) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun position => by ring
    _ = _ := by
      rw [integral_add gradientIntegrable errorIntegrable, integral_const_mul,
        integral_sub firstCrossIntegrable secondCrossIntegrable, cross]
      ring

end EulerNonuniqueness
