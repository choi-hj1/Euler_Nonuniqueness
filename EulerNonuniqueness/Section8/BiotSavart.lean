import EulerNonuniqueness.Definitions
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# Biot--Savart estimates for the compactness argument

The estimates concern the actual convolution kernel used in the Euler statements.
The cancellation estimate supplies the zero-circulation far-field bound in
the proof of Lemma 8.1.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace EulerNonuniqueness

theorem biotSavartKernel_zero : biotSavartKernel 0 = 0 := by
  simp [biotSavartKernel]

theorem biotSavartKernel_eq_conj_inv (position : Plane) :
    biotSavartKernel position =
      (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * (starRingEnd ℂ position)⁻¹ := by
  rw [Complex.inv_def (starRingEnd ℂ position)]
  simp only [biotSavartKernel, Complex.normSq_conj, Complex.conj_conj,
    Complex.normSq_eq_norm_sq, Complex.norm_conj, Complex.ofReal_inv, Complex.ofReal_mul,
    div_eq_mul_inv, mul_inv_rev]
  ring

theorem norm_biotSavartKernel (position : Plane) :
    ‖biotSavartKernel position‖ = 1 / (2 * Real.pi * ‖position‖) := by
  rw [biotSavartKernel_eq_conj_inv]
  simp [norm_mul, norm_div, norm_inv, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]

theorem measurable_biotSavartKernel : Measurable biotSavartKernel := by
  unfold biotSavartKernel
  fun_prop

theorem continuousAt_biotSavartKernel {position : Plane} (nonzero : position ≠ 0) :
    ContinuousAt biotSavartKernel position := by
  unfold biotSavartKernel
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact_mod_cast mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
      Real.pi_ne_zero) (pow_ne_zero 2 (norm_ne_zero_iff.mpr nonzero))

theorem norm_biotSavartKernel_sub {first second : Plane}
    (firstNonzero : first ≠ 0) (secondNonzero : second ≠ 0) :
    ‖biotSavartKernel first - biotSavartKernel second‖ =
      ‖first - second‖ / (2 * Real.pi * ‖first‖ * ‖second‖) := by
  have firstConjNonzero : starRingEnd ℂ first ≠ 0 := by simpa using firstNonzero
  have secondConjNonzero : starRingEnd ℂ second ≠ 0 := by simpa using secondNonzero
  have inverseDifference : (starRingEnd ℂ first)⁻¹ - (starRingEnd ℂ second)⁻¹ =
      (starRingEnd ℂ second - starRingEnd ℂ first) /
        (starRingEnd ℂ first * starRingEnd ℂ second) := by
    field_simp
  rw [biotSavartKernel_eq_conj_inv, biotSavartKernel_eq_conj_inv, ← mul_sub,
    inverseDifference]
  simp only [norm_mul, norm_div, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    ← map_sub, Complex.norm_conj, norm_sub_rev]
  ring

theorem norm_biotSavartKernel_sub_le {position source : Plane}
    (positionPositive : 0 < ‖position‖) (sourceBound : 2 * ‖source‖ ≤ ‖position‖) :
    ‖biotSavartKernel (position - source) - biotSavartKernel position‖ ≤
      ‖source‖ / (Real.pi * ‖position‖ ^ 2) := by
  have differenceBound : ‖position‖ / 2 ≤ ‖position - source‖ := by
    have := norm_sub_norm_le position source
    linarith
  have differencePositive : 0 < ‖position - source‖ := by linarith
  rw [norm_biotSavartKernel_sub (norm_pos_iff.mp differencePositive)
    (norm_pos_iff.mp positionPositive)]
  have numerator : ‖position - source - position‖ = ‖source‖ := by
    rw [show position - source - position = -source by abel, norm_neg]
  rw [numerator]
  apply div_le_div_of_nonneg_left (norm_nonneg source) (by positivity)
  have denominatorBound := mul_le_mul_of_nonneg_right differenceBound
    (show 0 ≤ 2 * Real.pi * ‖position‖ by positivity)
  nlinarith

theorem norm_biotSavartKernel_shift_le {position source : Plane}
    (positionPositive : 0 < ‖position‖) (sourceBound : 2 * ‖source‖ ≤ ‖position‖) :
    ‖biotSavartKernel (position - source)‖ ≤ 1 / (Real.pi * ‖position‖) := by
  have differenceBound : ‖position‖ / 2 ≤ ‖position - source‖ := by
    have := norm_sub_norm_le position source
    linarith
  rw [norm_biotSavartKernel]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [Real.pi_pos]

theorem aestronglyMeasurable_biotSavart {vorticity : Vorticity}
    (measurable : AEStronglyMeasurable vorticity volume) :
    AEStronglyMeasurable (biotSavart vorticity) volume := by
  have kernelMeasurable : Measurable
      (fun point : Plane × Plane => biotSavartKernel (point.1 - point.2)) :=
    measurable_biotSavartKernel.comp (measurable_fst.sub measurable_snd)
  exact (measurable.snd.smul kernelMeasurable.aestronglyMeasurable).integral_prod_right'

theorem integrable_biotSavart_integrand_of_support {vorticity : Vorticity}
    (integrable : Integrable vorticity) {radius : ℝ}
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {position : Plane} (positionPositive : 0 < ‖position‖)
    (farField : 2 * radius ≤ ‖position‖) :
    Integrable (fun source => vorticity source • biotSavartKernel (position - source)) := by
  apply (integrable.norm.mul_const (1 / (Real.pi * ‖position‖))).mono'
  · exact integrable.aestronglyMeasurable.smul
      ((measurable_biotSavartKernel.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall fun source => by
      by_cases nonzero : vorticity source = 0
      · simp [nonzero]
      · have sourceBound : ‖source‖ ≤ radius := by
          simpa using supportBound (Function.mem_support.mpr nonzero)
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left
          (norm_biotSavartKernel_shift_le positionPositive (by linarith)) (norm_nonneg _)

theorem biotSavart_eq_integral_sub_of_integral_zero {vorticity : Vorticity}
    (integrable : Integrable vorticity) (zeroMean : (∫ source, vorticity source) = 0)
    {position : Plane}
    (kernelIntegrable : Integrable
      (fun source => vorticity source • biotSavartKernel (position - source))) :
    biotSavart vorticity position =
      ∫ source, vorticity source •
        (biotSavartKernel (position - source) - biotSavartKernel position) := by
  simp_rw [smul_sub]
  rw [integral_sub kernelIntegrable (integrable.smul_const _), integral_smul_const, zeroMean]
  simp [biotSavart]

theorem norm_biotSavart_le_of_support_integral_zero {vorticity : Vorticity}
    (integrable : Integrable vorticity) (zeroMean : (∫ source, vorticity source) = 0)
    {radius : ℝ}
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {position : Plane} (positionPositive : 0 < ‖position‖)
    (farField : 2 * radius ≤ ‖position‖) :
    ‖biotSavart vorticity position‖ ≤
      (∫ source, |vorticity source|) * radius / (Real.pi * ‖position‖ ^ 2) := by
  have kernelIntegrable := integrable_biotSavart_integrand_of_support integrable
    supportBound positionPositive farField
  have differenceIntegrable : Integrable (fun source => vorticity source •
      (biotSavartKernel (position - source) - biotSavartKernel position)) := by
    simp_rw [smul_sub]
    exact kernelIntegrable.sub (integrable.smul_const _)
  have pointwise : ∀ source,
      ‖vorticity source • (biotSavartKernel (position - source) - biotSavartKernel position)‖ ≤
        |vorticity source| * (radius / (Real.pi * ‖position‖ ^ 2)) := by
    intro source
    by_cases nonzero : vorticity source = 0
    · simp [nonzero]
    · have sourceBound : ‖source‖ ≤ radius := by
        simpa using supportBound (Function.mem_support.mpr nonzero)
      rw [norm_smul, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (norm_biotSavartKernel_sub_le positionPositive (by linarith)).trans
        (div_le_div_of_nonneg_right sourceBound (by positivity))
  rw [biotSavart_eq_integral_sub_of_integral_zero integrable zeroMean kernelIntegrable]
  calc
    ‖∫ source, vorticity source •
        (biotSavartKernel (position - source) - biotSavartKernel position)‖ ≤
        ∫ source, ‖vorticity source •
          (biotSavartKernel (position - source) - biotSavartKernel position)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ source, |vorticity source| * (radius / (Real.pi * ‖position‖ ^ 2)) :=
      integral_mono differenceIntegrable.norm (integrable.abs.mul_const _) pointwise
    _ = (∫ source, |vorticity source|) * radius / (Real.pi * ‖position‖ ^ 2) := by
      rw [integral_mul_const]
      ring

theorem memLp_inverse_one_add_norm_sq :
    MemLp (fun position : Plane => (1 + ‖position‖ ^ 2)⁻¹) 2 volume := by
  apply (memLp_two_iff_integrable_sq
    (Measurable.aestronglyMeasurable (by fun_prop))).mpr
  have bracket : Integrable (fun position : Plane =>
      (1 + ‖position‖ ^ 2) ^ (-(4 : ℝ) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by norm_num [Complex.finrank_real_complex])
  convert bracket using 1
  ext position
  rw [show -(4 : ℝ) / 2 = -(2 : ℝ) by norm_num, Real.rpow_neg (by positivity)]
  simp [Real.rpow_two, inv_pow]

theorem memLp_biotSavart_farField {vorticity : Vorticity}
    (integrable : Integrable vorticity) (zeroMean : (∫ source, vorticity source) = 0)
    {radius : ℝ} (radiusNonnegative : 0 ≤ radius)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius) :
    MemLp (biotSavart vorticity) 2
      (volume.restrict {position : Plane | max (2 * radius) 1 ≤ ‖position‖}) := by
  let coefficient := (∫ source, |vorticity source|) * radius / Real.pi
  have coefficientNonnegative : 0 ≤ coefficient := by
    dsimp [coefficient]
    positivity
  apply (memLp_inverse_one_add_norm_sq.restrict _).of_le_mul
    (c := 2 * coefficient)
    (aestronglyMeasurable_biotSavart integrable.aestronglyMeasurable).restrict
  filter_upwards [ae_restrict_mem (measurableSet_le measurable_const (by fun_prop))]
    with position positionBound
  have positionOne : 1 ≤ ‖position‖ := (le_max_right _ _).trans positionBound
  have positionPositive : 0 < ‖position‖ := by linarith
  have farField : 2 * radius ≤ ‖position‖ := (le_max_left _ _).trans positionBound
  have normBound := norm_biotSavart_le_of_support_integral_zero integrable zeroMean
    supportBound positionPositive farField
  have bound : ‖biotSavart vorticity position‖ ≤ coefficient / ‖position‖ ^ 2 := by
    convert normBound using 1
    dsimp [coefficient]
    ring
  refine bound.trans ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have squareBound : 1 ≤ ‖position‖ ^ 2 := by nlinarith [norm_nonneg position]
  nlinarith

theorem integrableOn_inv_norm_ball (radius : ℝ) :
    IntegrableOn (fun position : Plane => ‖position‖⁻¹) (Metric.ball 0 radius) := by
  let integrand : Plane → ℝ :=
    (Metric.ball 0 radius).indicator (fun position : Plane => ‖position‖⁻¹)
  have integrandMeasurable : Measurable integrand := by
    dsimp [integrand]
    exact Measurable.indicator (by fun_prop) measurableSet_ball
  have integrandNonnegative : ∀ position, 0 ≤ integrand position := by
    intro position
    exact Set.indicator_nonneg (fun _ _ => by positivity) position
  have finiteIntegral : HasFiniteIntegral integrand := by
    rw [hasFiniteIntegral_iff_enorm]
    simp_rw [Real.enorm_eq_ofReal (integrandNonnegative _)]
    rw [← Complex.lintegral_comp_polarCoord_symm]
    let rectangle : Set (ℝ × ℝ) := Ioc 0 radius ×ˢ Ioo (-Real.pi) Real.pi
    have rectangleMeasurable : MeasurableSet rectangle :=
      measurableSet_Ioc.prod measurableSet_Ioo
    have rectangleFinite : volume rectangle < ∞ := by
      apply lt_of_le_of_lt (measure_mono
        (Set.prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self))
      exact (isCompact_Icc.prod isCompact_Icc).measure_lt_top
    have bound : ∀ point ∈ polarCoord.target,
        ENNReal.ofReal point.1 • ENNReal.ofReal (integrand (Complex.polarCoord.symm point)) ≤
          rectangle.indicator (fun _ => (1 : ℝ≥0∞)) point := by
      intro point pointTarget
      have radiusPositive : 0 < point.1 := pointTarget.1
      have angleBound : point.2 ∈ Ioo (-Real.pi) Real.pi := pointTarget.2
      by_cases inside : point.1 < radius
      · have complexInside : Complex.polarCoord.symm point ∈ Metric.ball 0 radius := by
          simpa [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm,
            abs_of_pos radiusPositive] using inside
        have rectangleInside : point ∈ rectangle := ⟨⟨radiusPositive, inside.le⟩, angleBound⟩
        simp only [integrand, Set.indicator_of_mem complexInside,
          Set.indicator_of_mem rectangleInside, Complex.norm_polarCoord_symm,
          abs_of_pos radiusPositive, smul_eq_mul]
        rw [← ENNReal.ofReal_mul radiusPositive.le, mul_inv_cancel₀ radiusPositive.ne']
        simp
      · have complexOutside : Complex.polarCoord.symm point ∉ Metric.ball 0 radius := by
          simpa [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm,
            abs_of_pos radiusPositive] using inside
        simp only [integrand, Set.indicator_of_not_mem complexOutside,
          ENNReal.ofReal_zero, smul_zero, zero_le]
    calc
      (∫⁻ point in polarCoord.target,
          ENNReal.ofReal point.1 • ENNReal.ofReal (integrand (Complex.polarCoord.symm point))) ≤
          ∫⁻ point in polarCoord.target, rectangle.indicator (fun _ => (1 : ℝ≥0∞)) point :=
        setLIntegral_mono' polarCoord.open_target.measurableSet bound
      _ ≤ ∫⁻ point, rectangle.indicator (fun _ => (1 : ℝ≥0∞)) point :=
        lintegral_mono' Measure.restrict_le_self le_rfl
      _ < ∞ := by
        rw [lintegral_indicator_const rectangleMeasurable, one_mul]
        exact rectangleFinite
  exact (integrable_indicator_iff measurableSet_ball).mp
    ⟨integrandMeasurable.aestronglyMeasurable, finiteIntegral⟩

theorem integrableOn_biotSavartKernel_ball (radius : ℝ) :
    IntegrableOn biotSavartKernel (Metric.ball 0 radius) := by
  apply ((integrableOn_inv_norm_ball radius).const_mul (1 / (2 * Real.pi))).mono'
    measurable_biotSavartKernel.aestronglyMeasurable.restrict
  exact Filter.Eventually.of_forall fun position => by
    rw [norm_biotSavartKernel]
    exact le_of_eq (by ring)

theorem locallyIntegrable_biotSavartKernel : LocallyIntegrable biotSavartKernel volume := by
  intro position
  refine ⟨Metric.ball 0 (‖position‖ + 1), ?_,
    integrableOn_biotSavartKernel_ball (‖position‖ + 1)⟩
  apply Metric.isOpen_ball.mem_nhds
  simp

theorem biotSavart_integrand_eq_truncated {vorticity : Vorticity} {radius : ℝ}
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {position : Plane} {cutoff : ℝ} (cutoffBound : ‖position‖ + radius < cutoff)
    (source : Plane) :
    vorticity source • (Metric.ball 0 cutoff).indicator biotSavartKernel (position - source) =
      vorticity source • biotSavartKernel (position - source) := by
  by_cases nonzero : vorticity source = 0
  · simp [nonzero]
  · have sourceBound : ‖source‖ ≤ radius := by
      simpa using supportBound (Function.mem_support.mpr nonzero)
    have inside : position - source ∈ Metric.ball 0 cutoff := by
      simp only [Metric.mem_ball, dist_zero_right]
      exact (norm_sub_le position source).trans_lt (by linarith)
    rw [Set.indicator_of_mem inside]

theorem biotSavartIntegrable_of_integrable_support {vorticity : Vorticity}
    (integrable : Integrable vorticity) {radius : ℝ}
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius) :
    BiotSavartIntegrable vorticity := by
  have truncatedIntegrable (cutoff : ℝ) :
      Integrable ((Metric.ball 0 cutoff).indicator biotSavartKernel) :=
    (integrable_indicator_iff measurableSet_ball).mpr
      (integrableOn_biotSavartKernel_ball cutoff)
  have almostEverywhere (index : ℕ) : ∀ᵐ position ∂(volume : Measure Plane),
      Integrable (fun source => vorticity source •
        (Metric.ball 0 ((index : ℝ) + radius + 1)).indicator biotSavartKernel
          (position - source)) := by
    exact (integrable.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ)
      (truncatedIntegrable ((index : ℝ) + radius + 1))).prod_right_ae
  filter_upwards [ae_all_iff.mpr almostEverywhere] with position allCutoffs
  obtain ⟨index, indexBound⟩ := exists_nat_gt ‖position‖
  apply (allCutoffs index).congr
  exact Filter.Eventually.of_forall
    (biotSavart_integrand_eq_truncated supportBound (by linarith))

theorem integrableOn_biotSavart_ball {vorticity : Vorticity}
    (integrable : Integrable vorticity) {radius : ℝ}
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (observationRadius : ℝ) :
    IntegrableOn (biotSavart vorticity) (Metric.ball 0 observationRadius) := by
  have kernelIntegrable :
      Integrable ((Metric.ball 0 (observationRadius + radius)).indicator biotSavartKernel) :=
    (integrable_indicator_iff measurableSet_ball).mpr
      (integrableOn_biotSavartKernel_ball (observationRadius + radius))
  have convolutionIntegrable := integrable.integrable_convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) kernelIntegrable
  refine convolutionIntegrable.integrableOn.congr_fun ?_ measurableSet_ball
  intro position inside
  change (∫ source, vorticity source •
    (Metric.ball 0 (observationRadius + radius)).indicator biotSavartKernel
      (position - source)) = biotSavart vorticity position
  apply integral_congr_ae
  have positionBound : ‖position‖ < observationRadius := by simpa using inside
  exact Filter.Eventually.of_forall
    (biotSavart_integrand_eq_truncated supportBound (by linarith))

theorem locallyIntegrable_biotSavart_of_integrable_support {vorticity : Vorticity}
    (integrable : Integrable vorticity) {radius : ℝ}
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius) :
    LocallyIntegrable (biotSavart vorticity) volume := by
  intro position
  refine ⟨Metric.ball 0 (‖position‖ + 1), ?_,
    integrableOn_biotSavart_ball integrable supportBound (‖position‖ + 1)⟩
  apply Metric.isOpen_ball.mem_nhds
  simp

theorem norm_biotSavart_le_of_bounded_support {vorticity : Vorticity}
    {radius bound observationRadius : ℝ}
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (vorticityBound : ∀ source, |vorticity source| ≤ bound)
    {position : Plane} (positionBound : ‖position‖ ≤ observationRadius) :
    ‖biotSavart vorticity position‖ ≤ bound *
      ∫ source, ‖(Metric.ball 0 (observationRadius + radius + 1)).indicator
        biotSavartKernel source‖ := by
  let truncated := (Metric.ball 0 (observationRadius + radius + 1)).indicator biotSavartKernel
  have truncatedIntegrable : Integrable truncated :=
    (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_biotSavartKernel_ball _)
  have dominantIntegrable : Integrable (fun source => bound * ‖truncated (position - source)‖) :=
    (truncatedIntegrable.norm.comp_sub_left position).const_mul bound
  have pointwise : ∀ source,
      ‖vorticity source • biotSavartKernel (position - source)‖ ≤
        bound * ‖truncated (position - source)‖ := by
    intro source
    rw [← biotSavart_integrand_eq_truncated supportBound
      (show ‖position‖ + radius < observationRadius + radius + 1 by linarith),
      norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (vorticityBound source) (norm_nonneg _)
  calc
    ‖biotSavart vorticity position‖ ≤ ∫ source, bound * ‖truncated (position - source)‖ :=
      norm_integral_le_of_norm_le dominantIntegrable (Filter.Eventually.of_forall pointwise)
    _ = bound * ∫ source, ‖truncated source‖ := by
      rw [integral_const_mul]
      congr 1
      exact integral_sub_left_eq_self (fun source => ‖truncated source‖) volume position

theorem integrable_biotSavart_integrand_of_bounded_support {vorticity : Vorticity}
    (measurable : AEStronglyMeasurable vorticity volume) {radius bound : ℝ}
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (vorticityBound : ∀ source, |vorticity source| ≤ bound) (position : Plane) :
    Integrable (fun source => vorticity source • biotSavartKernel (position - source)) := by
  let truncated := (Metric.ball 0 (‖position‖ + radius + 1)).indicator biotSavartKernel
  have truncatedIntegrable : Integrable truncated :=
    (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_biotSavartKernel_ball _)
  apply ((truncatedIntegrable.norm.comp_sub_left position).const_mul bound).mono'
  · exact measurable.smul
      (measurable_biotSavartKernel.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun source => by
      rw [← biotSavart_integrand_eq_truncated supportBound
        (show ‖position‖ + radius < ‖position‖ + radius + 1 by linarith),
        norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (vorticityBound source) (norm_nonneg _)

theorem memLp_biotSavart_closedBall_of_bounded_support {vorticity : Vorticity}
    (measurable : AEStronglyMeasurable vorticity volume) {radius bound : ℝ}
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (vorticityBound : ∀ source, |vorticity source| ≤ bound)
    (observationRadius : ℝ) (exponent : ℝ≥0∞) :
    MemLp (biotSavart vorticity) exponent (volume.restrict (Metric.closedBall 0 observationRadius)) := by
  letI : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Plane) observationRadius)) :=
    ⟨by simpa using (isCompact_closedBall (0 : Plane) observationRadius).measure_lt_top (μ := volume)⟩
  apply MemLp.of_bound (μ := volume.restrict (Metric.closedBall (0 : Plane) observationRadius))
    (aestronglyMeasurable_biotSavart measurable).restrict
    (bound * ∫ source, ‖(Metric.ball 0 (observationRadius + radius + 1)).indicator
      biotSavartKernel source‖)
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with position inside
  exact norm_biotSavart_le_of_bounded_support supportBound vorticityBound (by simpa using inside)

theorem memLp_biotSavart_two_of_bounded_support_integral_zero {vorticity : Vorticity}
    (integrable : Integrable vorticity) (zeroMean : (∫ source, vorticity source) = 0)
    {radius bound : ℝ} (radiusNonnegative : 0 ≤ radius)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (vorticityBound : ∀ source, |vorticity source| ≤ bound) :
    MemLp (biotSavart vorticity) 2 volume := by
  have measurable := aestronglyMeasurable_biotSavart integrable.aestronglyMeasurable
  have near := memLp_biotSavart_closedBall_of_bounded_support integrable.aestronglyMeasurable
    supportBound vorticityBound (max (2 * radius) 1) 2
  have far := memLp_biotSavart_farField integrable zeroMean radiusNonnegative supportBound
  have complement : MemLp (biotSavart vorticity) 2
      (volume.restrict (Metric.closedBall 0 (max (2 * radius) 1))ᶜ) := by
    apply far.mono_measure (Measure.restrict_mono ?_ le_rfl)
    intro position outside
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at outside
    exact outside.le
  apply (memLp_two_iff_integrable_sq_norm measurable).mpr
  have nearIntegral := (memLp_two_iff_integrable_sq_norm measurable.restrict).mp near
  have farIntegral := (memLp_two_iff_integrable_sq_norm measurable.restrict).mp complement
  have combined := (integrableOn_union.mpr ⟨nearIntegral, farIntegral⟩)
  simpa using combined

theorem integrableOn_norm_rpow_ball {exponent radius : ℝ}
    (exponentBound : -2 < exponent) (radiusPositive : 0 < radius) :
    IntegrableOn (fun position : Plane => ‖position‖ ^ exponent) (Metric.ball 0 radius) := by
  let integrand : Plane → ℝ :=
    (Metric.ball 0 radius).indicator (fun position : Plane => ‖position‖ ^ exponent)
  have integrandMeasurable : Measurable integrand := by
    dsimp [integrand]
    exact Measurable.indicator (by fun_prop) measurableSet_ball
  have radial : IntegrableOn (fun distance : ℝ => distance ^ (exponent + 1)) (Ioo 0 radius) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff radiusPositive).mpr (by linarith)
  have angular : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo (-Real.pi) Real.pi) :=
    (continuous_const.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have product := radial.mul_prod angular
  have productFinite : (∫⁻ point in Ioo 0 radius ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal (point.1 ^ (exponent + 1))) < ∞ := by
    have finite := product.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at finite
    simp only [mul_one] at finite
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at finite
    apply lt_of_le_of_lt _ finite
    apply setLIntegral_mono' (measurableSet_Ioo.prod measurableSet_Ioo)
    intro point inside
    rw [Real.enorm_eq_ofReal (Real.rpow_nonneg inside.1.1.le _)]
  have finiteIntegral : HasFiniteIntegral integrand := by
    rw [hasFiniteIntegral_iff_enorm]
    have nonnegative (position : Plane) : 0 ≤ integrand position :=
      Set.indicator_nonneg (fun position _ => Real.rpow_nonneg (norm_nonneg _) _) position
    simp_rw [Real.enorm_eq_ofReal (nonnegative _)]
    rw [← Complex.lintegral_comp_polarCoord_symm]
    calc
      (∫⁻ point in polarCoord.target,
          ENNReal.ofReal point.1 • ENNReal.ofReal (integrand (Complex.polarCoord.symm point))) =
          ∫⁻ point in Ioo 0 radius ×ˢ Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal (point.1 ^ (exponent + 1)) := by
        rw [← lintegral_indicator polarCoord.open_target.measurableSet,
          ← lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
        apply lintegral_congr
        intro point
        by_cases target : point ∈ polarCoord.target
        · have positive : 0 < point.1 := target.1
          by_cases inside : point.1 < radius
          · have complexInside : Complex.polarCoord.symm point ∈ Metric.ball 0 radius := by
              simpa [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm,
                abs_of_pos positive] using inside
            have rectangleInside : point ∈ Ioo 0 radius ×ˢ Ioo (-Real.pi) Real.pi :=
              ⟨⟨positive, inside⟩, target.2⟩
            simp only [Set.indicator_of_mem target, Set.indicator_of_mem rectangleInside,
              integrand, Set.indicator_of_mem complexInside, Complex.norm_polarCoord_symm,
              abs_of_pos positive, smul_eq_mul]
            rw [← ENNReal.ofReal_mul positive.le, Real.rpow_add positive]
            simp [Real.rpow_one, mul_comm]
          · have complexOutside : Complex.polarCoord.symm point ∉ Metric.ball 0 radius := by
              simpa [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm,
                abs_of_pos positive] using inside
            have rectangleOutside : point ∉ Ioo 0 radius ×ˢ Ioo (-Real.pi) Real.pi :=
              fun membership => inside membership.1.2
            rw [Set.indicator_of_mem target, Set.indicator_of_not_mem rectangleOutside]
            simp only [integrand, Set.indicator_of_not_mem complexOutside,
              ENNReal.ofReal_zero, smul_zero]
        · have rectangleOutside : point ∉ Ioo 0 radius ×ˢ Ioo (-Real.pi) Real.pi := by
            intro membership
            exact target ⟨membership.1.1, membership.2⟩
          rw [Set.indicator_of_not_mem target, Set.indicator_of_not_mem rectangleOutside]
      _ < ∞ := productFinite
  exact (integrable_indicator_iff measurableSet_ball).mp
    ⟨integrandMeasurable.aestronglyMeasurable, finiteIntegral⟩

theorem memLp_biotSavartKernel_ball {exponent radius : ℝ}
    (exponentPositive : 0 < exponent) (exponentBound : exponent < 2)
    (radiusPositive : 0 < radius) :
    MemLp biotSavartKernel (ENNReal.ofReal exponent)
      (volume.restrict (Metric.ball 0 radius)) := by
  apply (integrable_norm_rpow_iff
    measurable_biotSavartKernel.aestronglyMeasurable.restrict
    (by positivity) ENNReal.ofReal_ne_top).mp
  simp only [ENNReal.toReal_ofReal exponentPositive.le]
  have radial := (integrableOn_norm_rpow_ball (show -2 < -exponent by linarith)
    radiusPositive).const_mul ((2 * Real.pi)⁻¹ ^ exponent)
  apply radial.congr
  exact Filter.Eventually.of_forall fun position => by
    dsimp only
    rw [norm_biotSavartKernel]
    have inverseProduct : 1 / (2 * Real.pi * ‖position‖) =
        ‖position‖⁻¹ * (2 * Real.pi)⁻¹ := by
      rw [one_div, mul_inv_rev]
    rw [inverseProduct]
    rw [Real.mul_rpow (inv_nonneg.mpr (norm_nonneg _))
      (inv_nonneg.mpr (by positivity)), Real.inv_rpow (norm_nonneg _),
      Real.rpow_neg (norm_nonneg _)]
    ring

theorem integrable_biotSavart_integrand_of_memLp_support {vorticity : Vorticity}
    {exponent : ℝ≥0∞} {conjugate radius : ℝ}
    [ENNReal.HolderTriple exponent (ENNReal.ofReal conjugate) 1]
    (membership : MemLp vorticity exponent volume)
    (conjugatePositive : 0 < conjugate) (conjugateBound : conjugate < 2)
    (radiusNonnegative : 0 ≤ radius)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (position : Plane) :
    Integrable (fun source => vorticity source • biotSavartKernel (position - source)) := by
  have truncated := (memLp_indicator_iff_restrict measurableSet_ball).mpr
    (memLp_biotSavartKernel_ball conjugatePositive conjugateBound
      (show 0 < ‖position‖ + radius + 1 by positivity))
  have translated := truncated.comp_measurePreserving
    (volume.measurePreserving_sub_left position)
  have integrable := memLp_one_iff_integrable.mp (translated.smul membership)
  apply integrable.congr
  exact Filter.Eventually.of_forall
    (biotSavart_integrand_eq_truncated supportBound
      (show ‖position‖ + radius < ‖position‖ + radius + 1 by linarith))

theorem norm_biotSavart_le_of_memLp_support {vorticity : Vorticity}
    {exponent conjugate radius observationRadius : ℝ}
    (conjugacy : exponent.HolderConjugate conjugate)
    (membership : MemLp vorticity (ENNReal.ofReal exponent) volume)
    (conjugateBound : conjugate < 2)
    (radiusNonnegative : 0 ≤ radius) (observationNonnegative : 0 ≤ observationRadius)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {position : Plane} (positionBound : ‖position‖ ≤ observationRadius) :
    ‖biotSavart vorticity position‖ ≤
      (∫ source, ‖vorticity source‖ ^ exponent) ^ (1 / exponent) *
      (∫ source, ‖(Metric.ball 0 (observationRadius + radius + 1)).indicator
        biotSavartKernel source‖ ^ conjugate) ^ (1 / conjugate) := by
  let truncated := (Metric.ball 0 (observationRadius + radius + 1)).indicator biotSavartKernel
  have truncatedMember : MemLp truncated (ENNReal.ofReal conjugate) volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr
      (memLp_biotSavartKernel_ball conjugacy.symm.pos conjugateBound (by positivity))
  have translated := truncatedMember.comp_measurePreserving
    (volume.measurePreserving_sub_left position)
  have holder := integral_mul_norm_le_Lp_mul_Lq conjugacy membership.norm translated.norm
  simp only [norm_norm, Function.comp_apply] at holder
  have integralEquality : biotSavart vorticity position =
      ∫ source, vorticity source • truncated (position - source) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun source =>
      (biotSavart_integrand_eq_truncated supportBound
        (show ‖position‖ + radius < observationRadius + radius + 1 by linarith) source).symm
  rw [integralEquality]
  calc
    ‖∫ source, vorticity source • truncated (position - source)‖ ≤
        ∫ source, ‖vorticity source‖ * ‖truncated (position - source)‖ := by
      simpa only [norm_smul] using
        norm_integral_le_integral_norm (fun source => vorticity source • truncated (position - source))
    _ ≤ (∫ source, ‖vorticity source‖ ^ exponent) ^ (1 / exponent) *
        (∫ source, ‖truncated (position - source)‖ ^ conjugate) ^ (1 / conjugate) := holder
    _ = _ := by
      rw [integral_sub_left_eq_self (fun source => ‖truncated source‖ ^ conjugate) volume position]

theorem enorm_biotSavart_le_eLpNorm_of_memLp_support {vorticity : Vorticity}
    {exponent conjugate radius observationRadius : ℝ}
    (conjugacy : exponent.HolderConjugate conjugate)
    (membership : MemLp vorticity (ENNReal.ofReal exponent) volume)
    (conjugateBound : conjugate < 2)
    (radiusNonnegative : 0 ≤ radius) (observationNonnegative : 0 ≤ observationRadius)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {position : Plane} (positionBound : ‖position‖ ≤ observationRadius) :
    ENNReal.ofReal ‖biotSavart vorticity position‖ ≤
      eLpNorm vorticity (ENNReal.ofReal exponent) volume *
      eLpNorm ((Metric.ball 0 (observationRadius + radius + 1)).indicator biotSavartKernel)
        (ENNReal.ofReal conjugate) volume := by
  have truncatedMember := (memLp_indicator_iff_restrict measurableSet_ball).mpr
    (memLp_biotSavartKernel_ball conjugacy.symm.pos conjugateBound
      (show 0 < observationRadius + radius + 1 by positivity))
  have estimate := norm_biotSavart_le_of_memLp_support conjugacy membership conjugateBound
    radiusNonnegative observationNonnegative supportBound positionBound
  apply (ENNReal.ofReal_le_ofReal estimate).trans_eq
  rw [ENNReal.ofReal_mul (by positivity)]
  congr 1
  · rw [MemLp.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr conjugacy.pos).ne'
      ENNReal.ofReal_ne_top membership]
    simp only [ENNReal.toReal_ofReal conjugacy.pos.le, one_div]
  · rw [MemLp.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr conjugacy.symm.pos).ne'
      ENNReal.ofReal_ne_top truncatedMember]
    simp only [ENNReal.toReal_ofReal conjugacy.symm.pos.le, one_div]

theorem memLp_biotSavart_closedBall_of_memLp_support {vorticity : Vorticity}
    {exponent conjugate radius observationRadius : ℝ}
    (conjugacy : exponent.HolderConjugate conjugate)
    (membership : MemLp vorticity (ENNReal.ofReal exponent) volume)
    (conjugateBound : conjugate < 2)
    (radiusNonnegative : 0 ≤ radius) (observationNonnegative : 0 ≤ observationRadius)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (targetExponent : ℝ≥0∞) :
    MemLp (biotSavart vorticity) targetExponent
      (volume.restrict (Metric.closedBall 0 observationRadius)) := by
  letI : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Plane) observationRadius)) :=
    ⟨by simpa using (isCompact_closedBall (0 : Plane) observationRadius).measure_lt_top (μ := volume)⟩
  apply MemLp.of_bound
    (aestronglyMeasurable_biotSavart membership.aestronglyMeasurable).restrict
    ((∫ source, ‖vorticity source‖ ^ exponent) ^ (1 / exponent) *
      (∫ source, ‖(Metric.ball 0 (observationRadius + radius + 1)).indicator
        biotSavartKernel source‖ ^ conjugate) ^ (1 / conjugate))
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with position inside
  exact norm_biotSavart_le_of_memLp_support conjugacy membership conjugateBound
    radiusNonnegative observationNonnegative supportBound (by simpa using inside)

theorem memLp_biotSavart_two_of_memLp_support_integral_zero {vorticity : Vorticity}
    {exponent conjugate radius : ℝ}
    (conjugacy : exponent.HolderConjugate conjugate)
    (membership : MemLp vorticity (ENNReal.ofReal exponent) volume)
    (conjugateBound : conjugate < 2)
    (integrable : Integrable vorticity) (zeroMean : (∫ source, vorticity source) = 0)
    (radiusNonnegative : 0 ≤ radius)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius) :
    MemLp (biotSavart vorticity) 2 volume := by
  have measurable := aestronglyMeasurable_biotSavart integrable.aestronglyMeasurable
  have near := memLp_biotSavart_closedBall_of_memLp_support conjugacy membership conjugateBound
    radiusNonnegative (show 0 ≤ max (2 * radius) 1 by positivity) supportBound 2
  have far := memLp_biotSavart_farField integrable zeroMean radiusNonnegative supportBound
  have complement : MemLp (biotSavart vorticity) 2
      (volume.restrict (Metric.closedBall 0 (max (2 * radius) 1))ᶜ) := by
    apply far.mono_measure (Measure.restrict_mono ?_ le_rfl)
    intro position outside
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at outside
    exact outside.le
  apply (memLp_two_iff_integrable_sq_norm measurable).mpr
  have nearIntegral := (memLp_two_iff_integrable_sq_norm measurable.restrict).mp near
  have farIntegral := (memLp_two_iff_integrable_sq_norm measurable.restrict).mp complement
  have combined := (integrableOn_union.mpr ⟨nearIntegral, farIntegral⟩)
  simpa using combined

theorem continuous_biotSavart_of_continuous_compactSupport {vorticity : Vorticity}
    (continuous : Continuous vorticity) (compactSupport : HasCompactSupport vorticity) :
    Continuous (biotSavart vorticity) := by
  exact compactSupport.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    continuous locallyIntegrable_biotSavartKernel

theorem biotSavart_sub {first second : Vorticity}
    (firstIntegrable : BiotSavartIntegrable first)
    (secondIntegrable : BiotSavartIntegrable second) :
    biotSavart (first - second) =ᵐ[volume] biotSavart first - biotSavart second := by
  filter_upwards [firstIntegrable, secondIntegrable] with position firstAt secondAt
  change (∫ source, (first source - second source) • biotSavartKernel (position - source)) = _
  simp_rw [sub_smul]
  exact integral_sub firstAt secondAt

theorem biotSavart_add {first second : Vorticity}
    (firstIntegrable : BiotSavartIntegrable first)
    (secondIntegrable : BiotSavartIntegrable second) :
    biotSavart (first + second) =ᵐ[volume] biotSavart first + biotSavart second := by
  filter_upwards [firstIntegrable, secondIntegrable] with position firstAt secondAt
  change (∫ source, (first source + second source) • biotSavartKernel (position - source)) = _
  simp_rw [add_smul]
  exact integral_add firstAt secondAt

end EulerNonuniqueness
