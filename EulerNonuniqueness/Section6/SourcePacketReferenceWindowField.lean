import EulerNonuniqueness.Section6.SourcePacketReferenceField
import EulerNonuniqueness.Section6.PrehitNeutralFrequencyAbsorption

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FiniteMovingPatchFamily.reference_window_field_weighted_seed_absorption
    {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    {threshold constant start horizon distance : ℝ}
    (densities : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (evolution : FinitePatchEvolution scales family.patchMotion 2)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioLarge : 3072 ≤ scales.ratio) (constantNonnegative : 0 ≤ constant)
    (thresholdSmall : threshold ≤ 1 / 4)
    (coarse : ReferenceCoarseBounds scales family.patchMotion threshold constant)
    (startNonnegative : 0 ≤ start) (horizonNonnegative : 0 ≤ horizon) (windowBound : start + horizon ≤ 2)
    (distancePositive : 0 < distance) (source : Fin count) (location : ℝ → ℂ) (locationMeasurable : Measurable location)
    (locationFar : ∀ elapsed ∈ Icc 0 horizon,
      distance ≤ ‖location elapsed - quadrupoleCenter family.patchMotion (start + elapsed) source‖)
    (sourceSmall : scales.length (source.val + 1) / distance ≤ 1 / 1048576)
    (strainSmall : constant * scales.strain ≤ 1)
    (hessianSmall : (constant * scales.hessian * Real.exp 2) * distance ≤ 1 / 16384)
    (neutralScaleSmall : constant * scales.hessian * scales.length (source.val + 1) ^ 2 * 2 *
      Real.exp (2 * (constant * scales.strain)) ≤ scales.length (source.val + 1))
    (radiusBound : scales.radius (source.val + 1) ≤ scales.length (source.val + 1))
    (materialRadiusSmall : scales.radius (source.val + 1) *
      (1 + constant * (scales.omega (source.val + 1))⁻¹ ^ 2) ≤ scales.length (source.val + 1))
    (deformationSmall : constant * (scales.omega (source.val + 1))⁻¹ ^ 2 ≤ 1 / 16) :
    let decay := 2 * Real.sqrt 2 * scales.omega source.val
    let field := fun elapsed => Section6.vorticityComplexStrain
      (quadrupoleDensity scales family.patchMotion (start + elapsed) source) (location elapsed)
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * ‖field elapsed‖) volume 0 horizon ∧
    4 * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * ‖field elapsed‖) ≤
      (3 / 8 : ℝ) * (Real.sqrt 3 * scales.circulation (source.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega source.val ^ 2 * distance ^ 4)) := by
  have ratioPositive : 0 < scales.ratio := by linarith
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (source.val + 1)
  have receiverPositive := scales.omega_pos frequencyPositive ratioPositive source.val
  have lengthPositive := scales.length_pos (source.val + 1)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun index =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (scales.location_pos _).le _)
  let decay := 2 * Real.sqrt 2 * scales.omega source.val
  let field := fun elapsed => Section6.vorticityComplexStrain
    (quadrupoleDensity scales family.patchMotion (start + elapsed) source) (location elapsed)
  let neutralEnvelope := 2 * constant * scales.hessian * scales.length (source.val + 1) ^ 2 * Real.exp 2
  let momentEnvelope := 16 * scales.circulation (source.val + 1) * scales.length (source.val + 1) ^ 2 +
    512 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 *
      (constant * (scales.omega (source.val + 1))⁻¹ ^ 2)
  let envelope := 4 * scales.circulation (source.val + 1) * neutralEnvelope / (Real.pi * distance ^ 3) +
    3 * momentEnvelope / (2 * Real.pi * distance ^ 4) +
    352 * scales.circulation (source.val + 1) * (4 * scales.length (source.val + 1)) ^ 3 / (Real.pi * distance ^ 5)
  have momentNonnegative : 0 ≤ momentEnvelope := by dsimp only [momentEnvelope]; positivity
  have envelopeNonnegative : 0 ≤ envelope := by dsimp only [envelope, neutralEnvelope]; positivity
  have range (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : start + elapsed ∈ Icc 0 2 :=
    ⟨by linarith [inside.1], by linarith [inside.2]⟩
  have scaleSmall : 8 * scales.length (source.val + 1) ≤ distance := by
    have small := (div_le_iff₀ distancePositive).mp sourceSmall
    linarith
  have pointwise (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : ‖field elapsed‖ ≤ envelope := by
    have actual := evolution.reference_literal_strain_bound (range elapsed inside) amplitudePositive frequencyPositive
      ratioPositive constantNonnegative thresholdSmall coarse source (location elapsed) distancePositive
      (locationFar elapsed inside) scaleSmall neutralScaleSmall materialRadiusSmall
    have neutral := (coarse.2.1 (start + elapsed) (range elapsed inside) source).2.2.2.2.1
    have exponent : Real.exp (constant * scales.strain * (start + elapsed)) ≤ Real.exp 2 := by
      apply Real.exp_le_exp.mpr
      have timeNonnegative := (range elapsed inside).1
      have timeBound := (range elapsed inside).2
      nlinarith
    have neutralBound : ‖centroidAsymmetry family.patchMotion (start + elapsed) source‖ ≤ neutralEnvelope := by
      apply neutral.trans
      have upper := mul_le_mul (mul_le_mul_of_nonneg_left (range elapsed inside).2
        (show 0 ≤ constant * scales.hessian * scales.length (source.val + 1) ^ 2 by positivity))
        exponent (Real.exp_pos _).le (by positivity)
      convert upper using 1 <;> dsimp only [neutralEnvelope] <;> ring
    have momentBound := evolution.reference_literal_complex_moment_bound (range elapsed inside)
      amplitudePositive frequencyPositive ratioPositive constantNonnegative thresholdSmall coarse source deformationSmall
    apply actual.trans
    dsimp only [envelope]
    gcongr
  have physical := family.measurable_quadrupole_strain_along scales densities source
    (locationMeasurable.comp (measurable_id.sub_const start))
  have shifted := physical.comp (measurable_const.add measurable_id : Measurable (fun elapsed : ℝ => start + elapsed))
  have fieldMeasurable : Measurable field := by
    simpa only [Function.comp_def, id_eq, add_sub_cancel_left, field] using shifted
  have weightedMeasurable : Measurable (fun elapsed => Real.exp (-decay * elapsed) * ‖field elapsed‖) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul fieldMeasurable.norm
  have majorantIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * envelope) volume 0 horizon :=
    (by fun_prop : Continuous (fun elapsed : ℝ => Real.exp (-decay * elapsed) * envelope)).intervalIntegrable _ _
  have weightedBound (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      Real.exp (-decay * elapsed) * ‖field elapsed‖ ≤ Real.exp (-decay * elapsed) * envelope :=
    mul_le_mul_of_nonneg_left (pointwise elapsed inside) (Real.exp_pos _).le
  have actualIntegrable := majorantIntegrable.mono_fun' weightedMeasurable.aestronglyMeasurable.restrict (by
    rw [uIoc_of_le horizonNonnegative]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with elapsed inside
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
    exact weightedBound elapsed ⟨inside.1.le, inside.2⟩)
  have decayPositive : 0 < decay := by dsimp only [decay]; positivity
  have constantBound := Section6.laplace_affine_integral_bound decayPositive (by norm_num : (0 : ℝ) ≤ 0)
    envelopeNonnegative horizonNonnegative
  simp only [zero_mul, zero_add, zero_div, zero_add] at constantBound
  have integralBound := (intervalIntegral.integral_mono_on horizonNonnegative actualIntegrable majorantIntegrable weightedBound).trans constantBound
  have neutralAbsorption := scales.prehit_neutral_weighted_cost_absorption source.val frequencyPositive
    (by linarith : 1 ≤ scales.ratio) distancePositive
    (hessian := constant * scales.hessian * Real.exp 2) (by positivity)
    (initialNeutral := neutralEnvelope) (by
      have bound := mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 64)
        (show 0 ≤ (constant * scales.hessian * Real.exp 2) * scales.length (source.val + 1) ^ 2 by positivity)
      convert bound using 1 <;> dsimp only [neutralEnvelope] <;> ring)
    (strain := 0) receiverPositive.le hessianSmall
  have momentAbsorption := scales.initial_moment_weighted_cost_absorption source.val frequencyPositive ratioPositive
    distancePositive (outgoingRadius := 32) (by norm_num) (by norm_num; exact ratioLarge) radiusBound
    (by positivity) deformationSmall (momentEnvelope : ℂ) (by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg momentNonnegative]
      dsimp only [momentEnvelope]
      nlinarith [mul_nonneg circulationPositive.le (sq_nonneg (scales.length (source.val + 1)))])
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg momentNonnegative] at momentAbsorption
  have remainderAbsorption := scales.reference_multipole_remainder_weighted_seed_absorption source.val frequencyPositive
    (by linarith : 1 ≤ scales.ratio) distancePositive sourceSmall
  simp only [sub_zero] at neutralAbsorption
  refine ⟨actualIntegrable, ?_⟩
  have sumBounds := add_le_add (add_le_add neutralAbsorption momentAbsorption) remainderAbsorption
  apply (mul_le_mul_of_nonneg_left integralBound (by norm_num : (0 : ℝ) ≤ 4)).trans
  convert sumBounds using 1 <;> dsimp only [envelope, decay] <;> ring

end EulerNonuniqueness.Paper
