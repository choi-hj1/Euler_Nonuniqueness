import EulerNonuniqueness.Section3.PeriodicHilbert
import EulerNonuniqueness.Section3.C1HolderOperations
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

open MeasureTheory Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

def circleCauchyTranslatedRemainder (function : ℝ → ℂ) (target source : ℝ) : ℂ :=
  (function (source + target) - function target) * standardCircleTangent source /
    (standardCircle 0 - standardCircle source)

theorem circleCauchyTranslatedRemainder_eq (density : PeriodicHolderHalf) (target source : ℝ) :
    circleCauchyTranslatedRemainder density.val.1 target source =
      contourCauchyDensityRemainder standardCircle standardCircleTangent
        (holderLabelShift target density).val.1 0 source := by
  simp only [circleCauchyTranslatedRemainder, contourCauchyDensityRemainder,
    holderLabelShift_value, zero_add]

theorem circleCauchyCLM_translated (density : PeriodicHolderHalf) (target : ℝ) :
    (circleCauchyCLM density).val.1 target =
      (∫ source in (-Real.pi)..Real.pi,
        circleCauchyTranslatedRemainder density.val.1 target source) -
          (Real.pi : ℂ) * Complex.I * density.val.1 target := by
  have identity := congrArg (fun data : PeriodicHolderHalf => data.val.1 0)
    (circleCauchyCLM_shift target density)
  dsimp only at identity
  rw [holderLabelShift_value, zero_add] at identity
  rw [← identity]
  change contourCauchyTransform standardCircle standardCircleTangent
    (holderLabelShift target density).val.1 0 = _
  unfold contourCauchyTransform
  simp only [zero_sub, zero_add, holderLabelShift_value]
  simp_rw [circleCauchyTranslatedRemainder_eq]

theorem circleCauchyTranslatedRemainder_integrable (density : PeriodicHolderHalf) (target : ℝ) :
    IntervalIntegrable (circleCauchyTranslatedRemainder density.val.1 target)
      volume (-Real.pi) Real.pi := by
  have integrable := banachContourCauchy_density_integrable_centered standardCircleBanach
    (holderLabelShift target density) standardCircleBanach_near 0
  change IntervalIntegrable (contourCauchyDensityRemainder standardCircle standardCircleTangent
    (holderLabelShift target density).val.1 0) volume (0 - Real.pi) (0 + Real.pi) at integrable
  simp only [zero_sub, zero_add] at integrable
  convert integrable using 1
  funext source
  exact circleCauchyTranslatedRemainder_eq density target source

theorem circleCauchyTranslatedRemainder_bound (density : PeriodicHolderHalf) (target : ℝ)
    {source : ℝ} (inside : source ∈ Icc (-Real.pi) Real.pi) :
    ‖circleCauchyTranslatedRemainder density.val.1 target source‖ ≤
      (‖density‖ / (2 / Real.pi)) * inverseSqrtDistance 0 source := by
  rw [circleCauchyTranslatedRemainder_eq]
  have densityBound :
      ‖(holderLabelShift target density).val.1 source - (holderLabelShift target density).val.1 0‖ ≤
        ‖density‖ * Real.sqrt |source - 0| := by
    simpa only [holderLabelShift_value, zero_add, add_sub_cancel_right, sub_zero]
      using PeriodicHolderHalf.holder_bound density (source + target) target
  have chordBound : (2 / Real.pi) * |source - 0| ≤ ‖standardCircle 0 - standardCircle source‖ := by
    simpa only [sub_zero, norm_sub_rev] using standardCircle_chord_bound source inside
  simpa only [mul_one] using
    (contourCauchyDensityRemainder_bound_unordered (norm_nonneg density)
      (show (0 : ℝ) ≤ 1 by norm_num) (by positivity : 0 < 2 / Real.pi)
      densityBound (standardCircleTangent_norm source).le chordBound)

theorem circleCauchyCLM_hasDerivAt (data : PeriodicC1HolderHalf) (target : ℝ) :
    HasDerivAt (fun position => (circleCauchyCLM (c1ValueHolder data)).val.1 position)
      ((circleCauchyCLM data.val.2).val.1 target) target := by
  let integrand := circleCauchyTranslatedRemainder data.val.1
  let differentiated := circleCauchyTranslatedRemainder data.val.2.val.1
  have measurable (position : ℝ) : AEStronglyMeasurable (integrand position)
      (volume.restrict (uIoc (-Real.pi) Real.pi)) := by
    apply Measurable.aestronglyMeasurable
    exact (((data.val.1.continuous.comp (continuous_id.add continuous_const)).measurable.sub
      measurable_const).mul
      (continuous_iff_continuousAt.mpr (fun source =>
        (standardCircleTangent_derivative source).continuousAt)).measurable).div
      (measurable_const.sub (continuous_iff_continuousAt.mpr
        (fun source => (standardCircle_derivative source).continuousAt)).measurable)
  have derivativeMeasurable : AEStronglyMeasurable (differentiated target)
      (volume.restrict (uIoc (-Real.pi) Real.pi)) := by
    apply Measurable.aestronglyMeasurable
    exact (((data.val.2.val.1.continuous.comp (continuous_id.add continuous_const)).measurable.sub
      measurable_const).mul
      (continuous_iff_continuousAt.mpr (fun source =>
        (standardCircleTangent_derivative source).continuousAt)).measurable).div
      (measurable_const.sub (continuous_iff_continuousAt.mpr
        (fun source => (standardCircle_derivative source).continuousAt)).measurable)
  have derivative (position source : ℝ) :
      HasDerivAt (fun current => integrand current source) (differentiated position source) position := by
    have inner : HasDerivAt (fun current : ℝ => source + current) 1 position := by
      simpa only [id_eq] using (hasDerivAt_id position).const_add source
    have shifted := (PeriodicC1HolderHalf.hasDerivAt data (source + position)).scomp position inner
    simpa only [one_smul] using
      ((shifted.sub (PeriodicC1HolderHalf.hasDerivAt data position)).mul_const
        (standardCircleTangent source)).div_const (standardCircle 0 - standardCircle source)
  have integralDerivative := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := integrand) (F' := differentiated) (x₀ := target) (ε := 1)
    (bound := fun source => (‖data.val.2‖ / (2 / Real.pi)) * inverseSqrtDistance 0 source)
    (by norm_num) (Filter.Eventually.of_forall measurable)
    (circleCauchyTranslatedRemainder_integrable (c1ValueHolder data) target)
    derivativeMeasurable
    (Filter.Eventually.of_forall (fun source inside position _ =>
      circleCauchyTranslatedRemainder_bound data.val.2 position
        (by
          rw [uIoc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] at inside
          exact ⟨inside.1.le, inside.2⟩)))
    ((inverseSqrtDistance_integrable_symmetric Real.pi_pos).const_mul _)
    (Filter.Eventually.of_forall (fun source _ position _ => derivative position source))
  have result := integralDerivative.2.sub
    ((PeriodicC1HolderHalf.hasDerivAt data target).const_mul ((Real.pi : ℂ) * Complex.I))
  simpa only [circleCauchyCLM_translated, c1ValueHolder_value] using result

theorem periodicHilbertCLM_hasDerivAt (data : PeriodicC1HolderHalf) (target : ℝ) :
    HasDerivAt (fun position => (periodicHilbertCLM (c1ValueHolder data)).val.1 position)
      ((periodicHilbertCLM data.val.2).val.1 target) target := by
  have embedding : c1ValueHolder (c1Conjugate data) = holderConjugate (c1ValueHolder data) := by
    apply PeriodicHolderHalf.ext_value
    intro label
    rfl
  have first := circleCauchyCLM_hasDerivAt data target
  have second := (circleCauchyCLM_hasDerivAt (c1Conjugate data) target).star
  rw [embedding] at second
  change HasDerivAt
    (fun position => (1 / (2 * Real.pi)) •
      ((circleCauchyCLM (c1ValueHolder data)).val.1 position +
        star ((circleCauchyCLM (holderConjugate (c1ValueHolder data))).val.1 position)))
    ((1 / (2 * Real.pi)) •
      ((circleCauchyCLM data.val.2).val.1 target +
        star ((circleCauchyCLM (holderConjugate data.val.2)).val.1 target))) target
  exact (first.add second).const_smul (1 / (2 * Real.pi))

end

end EulerNonuniqueness.Paper
