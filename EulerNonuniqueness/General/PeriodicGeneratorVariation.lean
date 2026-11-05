import EulerNonuniqueness.General.LinearGroupPerturbation
import EulerNonuniqueness.General.LinearGroupGenerator
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace EulerNonuniqueness.General

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem periodicGeneratorVariation_integral_zero
    (family : ℝ → ℝ → Space →L[ℝ] Space) (operator : ℝ → Space →L[ℝ] Space)
    (variation : Space →L[ℝ] Space) {period : ℝ} (periodPositive : 0 < period)
    (jointContinuous : Continuous (fun pair : ℝ × ℝ => family pair.1 pair.2))
    (atZero : ∀ parameter, family parameter 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ parameter first second,
      family parameter (first + second) = (family parameter first).comp (family parameter second))
    (timeDerivative : ∀ parameter time,
      HasDerivAt (family parameter) ((operator parameter).comp (family parameter time)) time)
    (operatorDerivative : HasDerivAt operator variation 0)
    (periodic : ∀ᶠ parameter in 𝓝 (0 : ℝ), family parameter period = ContinuousLinearMap.id ℝ Space)
    (initial : Space) :
    (∫ time in (0 : ℝ)..period,
      family 0 (period - time) (variation (family 0 time initial))) = 0 := by
  let quotient := fun parameter : ℝ => parameter⁻¹ • (operator parameter - operator 0)
  let integrand := fun parameter time : ℝ =>
    family 0 (period - time) (quotient parameter (family parameter time initial))
  have slope : Tendsto quotient (𝓝[≠] (0 : ℝ)) (𝓝 variation) := by
    simpa only [quotient, zero_add] using operatorDerivative.tendsto_slope_zero
  have baseDerivative (time : ℝ) :
      HasDerivAt (family 0) ((family 0 time).comp (operator 0)) time := by
    have actual := linearGroup_hasDerivAt_right_generator (family 0)
      (fun time => (operator 0).comp (family 0 time)) (addition 0) (timeDerivative 0) time
    simpa only [atZero, ContinuousLinearMap.comp_id] using actual
  obtain ⟨bound, bounded⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) period) jointContinuous.continuousOn
  let constant := max bound 0
  have constantNonnegative : 0 ≤ constant := le_max_right _ _
  have familyBound {parameter time : ℝ} (parameterInside : parameter ∈ Icc (-1 : ℝ) 1)
      (timeInside : time ∈ Icc (0 : ℝ) period) : ‖family parameter time‖ ≤ constant :=
    (bounded (parameter, time) ⟨parameterInside, timeInside⟩).trans (le_max_left _ _)
  have nearParameter : ∀ᶠ parameter in 𝓝[≠] (0 : ℝ), parameter ∈ Icc (-1 : ℝ) 1 :=
    nhdsWithin_le_nhds (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
  have quotientBound : ∀ᶠ parameter in 𝓝[≠] (0 : ℝ), ‖quotient parameter‖ ≤ ‖variation‖ + 1 :=
    (slope.norm.eventually (eventually_lt_nhds (by linarith : ‖variation‖ < ‖variation‖ + 1))).mono
      (fun _ bound => bound.le)
  have continuousSlice (parameter : ℝ) : Continuous (family parameter) :=
    jointContinuous.comp (continuous_const.prodMk continuous_id)
  have continuousIntegrand (parameter : ℝ) : Continuous (integrand parameter) := by
    exact ((continuousSlice 0).comp (continuous_const.sub continuous_id)).clm_apply
      ((quotient parameter).continuous.comp ((continuousSlice parameter).clm_apply continuous_const))
  have integralLimit : Tendsto (fun parameter => ∫ time in (0 : ℝ)..period, integrand parameter time)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (∫ time in (0 : ℝ)..period,
        family 0 (period - time) (variation (family 0 time initial)))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => constant * ((‖variation‖ + 1) * (constant * ‖initial‖)))
    · exact Filter.Eventually.of_forall (fun parameter => (continuousIntegrand parameter).aestronglyMeasurable)
    · filter_upwards [nearParameter, quotientBound] with parameter parameterInside quotientSmall
      filter_upwards [] with time timeInside
      have inside : time ∈ Icc (0 : ℝ) period := by
        rw [uIoc_of_le periodPositive.le] at timeInside
        exact ⟨timeInside.1.le, timeInside.2⟩
      have backwardInside : period - time ∈ Icc (0 : ℝ) period := by constructor <;> linarith [inside.1, inside.2]
      dsimp only [integrand]
      calc
        _ ≤ ‖family 0 (period - time)‖ * (‖quotient parameter‖ *
            (‖family parameter time‖ * ‖initial‖)) := by
          exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))) (norm_nonneg _))
        _ ≤ _ := by
          gcongr
          · exact familyBound (by constructor <;> norm_num) backwardInside
          · exact familyBound parameterInside inside
    · exact intervalIntegrable_const
    · filter_upwards [] with time timeInside
      have familyLimit : Tendsto (fun parameter => family parameter time initial)
          (𝓝[≠] (0 : ℝ)) (𝓝 (family 0 time initial)) :=
        (((jointContinuous.comp (continuous_id.prodMk continuous_const)).clm_apply continuous_const).tendsto 0).mono_left
          nhdsWithin_le_nhds
      have evaluation : Continuous (fun pair : (Space →L[ℝ] Space) × Space => pair.1 pair.2) :=
        continuous_fst.clm_apply continuous_snd
      exact (family 0 (period - time)).continuous.continuousAt.tendsto.comp
        (evaluation.continuousAt.tendsto.comp (slope.prodMk_nhds familyLimit))
  have integralZero : ∀ᶠ parameter in 𝓝[≠] (0 : ℝ),
      (∫ time in (0 : ℝ)..period, integrand parameter time) = 0 := by
    have basePeriod : family 0 period = ContinuousLinearMap.id ℝ Space := periodic.self_of_nhds
    filter_upwards [periodic.filter_mono nhdsWithin_le_nhds] with parameter currentPeriod
    have equation (time : ℝ) (_inside : time ∈ Icc (0 : ℝ) period) :
        HasDerivAt (fun current => family parameter current initial)
          (operator parameter (family parameter time initial)) time := by
      simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero] using
        (timeDerivative parameter time).clm_apply (hasDerivAt_const time initial)
    have actual := linearGroup_perturbation_formula (family 0) (operator 0) (operator parameter)
      (atZero 0) (addition 0) baseDerivative (fun time => family parameter time initial)
      ((continuousSlice parameter).clm_apply continuous_const).continuousOn equation
      (show period ∈ Icc (0 : ℝ) period from ⟨periodPositive.le, le_rfl⟩)
    dsimp only at actual
    simp only [currentPeriod, basePeriod, atZero, ContinuousLinearMap.id_apply, sub_self] at actual
    have normalized := congrArg (fun value : Space => parameter⁻¹ • value) actual.symm
    dsimp only at normalized
    rw [smul_zero, ← intervalIntegral.integral_smul] at normalized
    convert normalized using 1
    apply intervalIntegral.integral_congr
    intro time _inside
    simp only [integrand, quotient, ContinuousLinearMap.smul_apply, map_smul]
  exact tendsto_nhds_unique integralLimit
    (tendsto_const_nhds.congr' (integralZero.mono (fun _ equality => equality.symm)))

end

end EulerNonuniqueness.General
