import EulerNonuniqueness.Section6.SourcePacketReferenceWindowField
import EulerNonuniqueness.Section6.LaplaceSourceErrorBound

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FiniteMovingPatchFamily.reference_window_field_arbitrary_weighted_budget
    {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    {threshold constant start horizon distance tolerance : ℝ}
    (densities : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (evolution : FinitePatchEvolution scales family.patchMotion 2)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (tolerancePositive : 0 < tolerance)
    (ratioBudget : 512 ≤ tolerance * scales.ratio) (constantNonnegative : 0 ≤ constant)
    (thresholdSmall : threshold ≤ 1 / 4)
    (coarse : ReferenceCoarseBounds scales family.patchMotion threshold constant)
    (startNonnegative : 0 ≤ start) (horizonNonnegative : 0 ≤ horizon) (windowBound : start + horizon ≤ 2)
    (distancePositive : 0 < distance) (source : Fin count) (location : ℝ → ℂ) (locationMeasurable : Measurable location)
    (locationFar : ∀ elapsed ∈ Icc 0 horizon,
      distance ≤ ‖location elapsed - quadrupoleCenter family.patchMotion (start + elapsed) source‖)
    (sourceSmall : scales.length (source.val + 1) / distance ≤ 1 / 1048576)
    (strainSmall : constant * scales.strain ≤ 1)
    (hessianSmall : (constant * scales.hessian * Real.exp 2) * distance ≤ 1)
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
      tolerance * (Real.sqrt 3 * scales.circulation (source.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega source.val ^ 2 * distance ^ 4)) := by
  have ratioPositive : 0 < scales.ratio := by linarith
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (source.val + 1)
  have receiverPositive := scales.omega_pos frequencyPositive ratioPositive source.val
  have lengthPositive := scales.length_pos (source.val + 1)
  have radiusPositive := scales.radius_pos amplitudePositive frequencyPositive ratioPositive (source.val + 1)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun index =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (scales.location_pos _).le _)
  let decay := 2 * Real.sqrt 2 * scales.omega source.val
  let field := fun elapsed => Section6.vorticityComplexStrain
    (quadrupoleDensity scales family.patchMotion (start + elapsed) source) (location elapsed)
  let neutralEnvelope := 2 * constant * scales.hessian * scales.length (source.val + 1) ^ 2 * Real.exp 2
  let momentEnvelope := 48 * scales.circulation (source.val + 1) * scales.length (source.val + 1) ^ 2
  let envelope := 4 * scales.circulation (source.val + 1) * neutralEnvelope / (Real.pi * distance ^ 3) +
    3 * momentEnvelope / (2 * Real.pi * distance ^ 4) +
    352 * scales.circulation (source.val + 1) * (4 * scales.length (source.val + 1)) ^ 3 / (Real.pi * distance ^ 5)
  have envelopeNonnegative : 0 ≤ envelope := by dsimp only [envelope, neutralEnvelope, momentEnvelope]; positivity
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
    have radiusSquare := pow_le_pow_left₀ (Real.sqrt_nonneg _) radiusBound 2
    have deformationNonnegative : 0 ≤ constant * (scales.omega (source.val + 1))⁻¹ ^ 2 := by positivity
    have patchError : 512 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 *
        (constant * (scales.omega (source.val + 1))⁻¹ ^ 2) ≤
        32 * scales.circulation (source.val + 1) * scales.length (source.val + 1) ^ 2 := by
      calc
        _ ≤ 512 * scales.circulation (source.val + 1) * scales.length (source.val + 1) ^ 2 * (1 / 16) := by gcongr
        _ = _ := by ring
    have momentCoarse : ‖∫ position, quadrupoleDensity scales family.patchMotion (start + elapsed) source position •
        (position - quadrupoleCenter family.patchMotion (start + elapsed) source) ^ 2‖ ≤ momentEnvelope := by
      dsimp only [momentEnvelope]
      linarith
    apply actual.trans
    dsimp only [envelope]
    gcongr
  have physical := family.measurable_quadrupole_strain_along scales densities source
    (locationMeasurable.comp (measurable_id.sub_const start))
  have shifted := physical.comp (measurable_const.add measurable_id : Measurable (fun elapsed : ℝ => start + elapsed))
  have fieldMeasurable : Measurable field := by
    simpa only [Function.comp_def, id_eq, add_sub_cancel_left, field] using shifted
  have decayPositive : 0 < decay := by dsimp only [decay]; positivity
  have bound := Section6.laplace_source_error_bound (error := field) (first := fun _ => (0 : ℂ))
    (second := fun _ => (0 : ℂ)) (constant := envelope) (firstCoefficient := 0) (secondCoefficient := 0)
    fieldMeasurable continuous_const continuous_const decayPositive envelopeNonnegative (by norm_num) (by norm_num)
    horizonNonnegative (by intro elapsed inside; simpa only [zero_mul, add_zero] using pointwise elapsed inside)
  simp only [zero_mul, add_zero] at bound
  have sqrtThreeLower : 1 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have factorBound : (16 * (constant * scales.hessian * Real.exp 2 * distance) + 144 +
      45056 * (scales.length (source.val + 1) / distance)) / (Real.sqrt 3 * scales.ratio) ≤ tolerance := by
    apply (div_le_iff₀ (mul_pos (by positivity : 0 < Real.sqrt 3) ratioPositive)).mpr
    calc
      _ ≤ 512 := by nlinarith
      _ ≤ tolerance * scales.ratio := ratioBudget
      _ ≤ tolerance * (Real.sqrt 3 * scales.ratio) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left ratioPositive.le sqrtThreeLower) tolerancePositive.le
  have omegaNext : scales.omega (source.val + 1) = scales.ratio * scales.omega source.val := by
    simp only [Scales.omega, pow_succ]
    ring
  have identity : 4 * (envelope / decay) =
      ((16 * (constant * scales.hessian * Real.exp 2 * distance) + 144 +
        45056 * (scales.length (source.val + 1) / distance)) / (Real.sqrt 3 * scales.ratio)) *
      (Real.sqrt 3 * scales.circulation (source.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega source.val ^ 2 * distance ^ 4)) := by
    dsimp only [envelope, neutralEnvelope, momentEnvelope, decay]
    simp only [Scales.circulation, omegaNext]
    field_simp [Real.pi_ne_zero, distancePositive.ne', (show 0 < Real.sqrt 2 by positivity).ne',
      (show 0 < Real.sqrt 3 by positivity).ne', receiverPositive.ne', ratioPositive.ne']
    <;> ring
  refine ⟨bound.1, ?_⟩
  exact (mul_le_mul_of_nonneg_left bound.2 (by norm_num : (0 : ℝ) ≤ 4)).trans
    (identity.le.trans (mul_le_mul_of_nonneg_right factorBound (by positivity)))

end EulerNonuniqueness.Paper
