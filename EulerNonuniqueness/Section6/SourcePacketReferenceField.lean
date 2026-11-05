import EulerNonuniqueness.Section6.SourcePacketReferenceStrain
import EulerNonuniqueness.Section6.SourcePacketReferenceAbsorption
import EulerNonuniqueness.Section6.SourcePacketReferenceNeutral
import EulerNonuniqueness.Section6.SourcePacketReferenceRemainder
import EulerNonuniqueness.Section6.MovingPatchStrainMeasurability

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FiniteMovingPatchFamily.reference_literal_field_weighted_seed_absorption
    {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    {threshold constant horizon distance : ℝ}
    (densities : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (evolution : FinitePatchEvolution scales family.patchMotion 2)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioLarge : 3072 ≤ scales.ratio) (constantNonnegative : 0 ≤ constant)
    (thresholdSmall : threshold ≤ 1 / 4)
    (coarse : ReferenceCoarseBounds scales family.patchMotion threshold constant)
    (horizonNonnegative : 0 ≤ horizon) (horizonBound : horizon ≤ 2) (distancePositive : 0 < distance)
    (source : Fin count) (location : ℝ → ℂ) (locationMeasurable : Measurable location)
    (locationFar : ∀ elapsed ∈ Icc 0 horizon,
      distance ≤ ‖location elapsed - quadrupoleCenter family.patchMotion elapsed source‖)
    (sourceSmall : scales.length (source.val + 1) / distance ≤ 1 / 1048576)
    (sourceFrequencyLarge : 1 ≤ scales.omega (source.val + 1))
    (strainSmall : constant * scales.strain ≤ scales.omega source.val)
    (hessianSmall : (constant * scales.hessian) * distance ≤ 1 / 16384)
    (neutralScaleSmall : constant * scales.hessian * scales.length (source.val + 1) ^ 2 * 2 *
      Real.exp (2 * (constant * scales.strain)) ≤ scales.length (source.val + 1))
    (radiusBound : scales.radius (source.val + 1) ≤ scales.length (source.val + 1))
    (materialRadiusSmall : scales.radius (source.val + 1) *
      (1 + constant * (scales.omega (source.val + 1))⁻¹ ^ 2) ≤ scales.length (source.val + 1))
    (deformationSmall : constant * (scales.omega (source.val + 1))⁻¹ ^ 2 ≤ 1 / 16) :
    let decay := 2 * Real.sqrt 2 * scales.omega source.val
    let field := fun elapsed => Section6.vorticityComplexStrain
      (quadrupoleDensity scales family.patchMotion elapsed source) (location elapsed)
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * ‖field elapsed‖) volume 0 horizon ∧
    4 * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * ‖field elapsed‖) ≤
      (3 / 8 : ℝ) * (Real.sqrt 3 * scales.circulation (source.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega source.val ^ 2 * distance ^ 4)) := by
  have ratioPositive : 0 < scales.ratio := by linarith
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (source.val + 1)
  have lengthPositive := scales.length_pos (source.val + 1)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun index =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (scales.location_pos _).le _)
  let decay := 2 * Real.sqrt 2 * scales.omega source.val
  let weight := fun elapsed => Real.exp (-decay * elapsed)
  let neutral := fun elapsed => ‖centroidAsymmetry family.patchMotion elapsed source‖
  let moment := fun elapsed => ‖∫ position, quadrupoleDensity scales family.patchMotion elapsed source position •
    (position - quadrupoleCenter family.patchMotion elapsed source) ^ 2‖
  let field := fun elapsed => Section6.vorticityComplexStrain
    (quadrupoleDensity scales family.patchMotion elapsed source) (location elapsed)
  let neutralCoefficient := 4 * scales.circulation (source.val + 1) / (Real.pi * distance ^ 3)
  let momentCoefficient := 3 / (2 * Real.pi * distance ^ 4)
  let remainder := 352 * scales.circulation (source.val + 1) * (4 * scales.length (source.val + 1)) ^ 3 /
    (Real.pi * distance ^ 5)
  have weightContinuous : Continuous weight := by dsimp only [weight]; fun_prop
  have neutralContinuous : Continuous neutral :=
    (((((family.patchCentroid_continuous source 0).add (family.patchCentroid_continuous source 1)).sub
      (family.patchCentroid_continuous source 2)).sub (family.patchCentroid_continuous source 3)).div_const 4).norm
  have momentContinuous : Continuous moment := (family.quadrupole_complex_moment_continuous scales source).norm
  have neutralIntegrable : IntervalIntegrable (fun elapsed => weight elapsed * neutral elapsed) volume 0 horizon :=
    (weightContinuous.mul neutralContinuous).intervalIntegrable 0 horizon
  have momentIntegrable : IntervalIntegrable (fun elapsed => weight elapsed * moment elapsed) volume 0 horizon :=
    (weightContinuous.mul momentContinuous).intervalIntegrable 0 horizon
  have remainderIntegrable : IntervalIntegrable (fun elapsed => weight elapsed * remainder) volume 0 horizon :=
    (weightContinuous.mul continuous_const).intervalIntegrable 0 horizon
  let majorant := fun elapsed => neutralCoefficient * (weight elapsed * neutral elapsed) +
    momentCoefficient * (weight elapsed * moment elapsed) + weight elapsed * remainder
  have majorantIntegrable : IntervalIntegrable majorant volume 0 horizon :=
    ((neutralIntegrable.const_mul neutralCoefficient).add
      (momentIntegrable.const_mul momentCoefficient)).add remainderIntegrable
  have scaleSmall : 8 * scales.length (source.val + 1) ≤ distance := by
    have small := (div_le_iff₀ distancePositive).mp sourceSmall
    linarith
  have pointwise (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      weight elapsed * ‖field elapsed‖ ≤ majorant elapsed := by
    have actual := evolution.reference_literal_strain_bound ⟨inside.1, inside.2.trans horizonBound⟩
      amplitudePositive frequencyPositive ratioPositive constantNonnegative thresholdSmall coarse source (location elapsed)
      distancePositive (locationFar elapsed inside) scaleSmall neutralScaleSmall materialRadiusSmall
    have weighted := mul_le_mul_of_nonneg_left actual (Real.exp_pos (-decay * elapsed)).le
    convert weighted using 1 <;> dsimp only [field, majorant, neutralCoefficient, momentCoefficient,
      neutral, moment, weight, remainder] <;> ring
  have fieldMeasurable := family.measurable_quadrupole_strain_along scales densities source locationMeasurable
  have measurable : Measurable (fun elapsed => weight elapsed * ‖field elapsed‖) :=
    weightContinuous.measurable.mul fieldMeasurable.norm
  have actualIntegrable := majorantIntegrable.mono_fun' measurable.aestronglyMeasurable.restrict (by
    rw [uIoc_of_le horizonNonnegative]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with elapsed inside
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
    exact pointwise elapsed ⟨inside.1.le, inside.2⟩)
  have integralBound := intervalIntegral.integral_mono_on horizonNonnegative actualIntegrable majorantIntegrable pointwise
  change (∫ elapsed in (0 : ℝ)..horizon, weight elapsed * ‖field elapsed‖) ≤ _ at integralBound
  have majorantEquation : (∫ elapsed in (0 : ℝ)..horizon, majorant elapsed) =
      neutralCoefficient * (∫ elapsed in (0 : ℝ)..horizon, weight elapsed * neutral elapsed) +
      momentCoefficient * (∫ elapsed in (0 : ℝ)..horizon, weight elapsed * moment elapsed) +
      (∫ elapsed in (0 : ℝ)..horizon, weight elapsed * remainder) := by
    rw [show majorant = (fun elapsed => (neutralCoefficient * (weight elapsed * neutral elapsed) +
      momentCoefficient * (weight elapsed * moment elapsed)) + weight elapsed * remainder) from rfl,
      intervalIntegral.integral_add ((neutralIntegrable.const_mul _).add (momentIntegrable.const_mul _)) remainderIntegrable,
      intervalIntegral.integral_add (neutralIntegrable.const_mul _) (momentIntegrable.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [majorantEquation] at integralBound
  have neutralBound := family.reference_neutral_weighted_seed_absorption scales frequencyPositive ratioPositive
    constantNonnegative hessianNonnegative coarse horizonNonnegative horizonBound distancePositive source sourceFrequencyLarge
    strainSmall hessianSmall radiusBound
  have momentBound := family.reference_literal_moment_weighted_seed_absorption scales evolution amplitudePositive
    frequencyPositive ratioLarge constantNonnegative thresholdSmall coarse horizonNonnegative horizonBound distancePositive
    source radiusBound deformationSmall
  have decayPositive : 0 < decay := by
    have receiverPositive := scales.omega_pos frequencyPositive ratioPositive source.val
    dsimp only [decay]
    positivity
  have remainderBound := Section6.laplace_affine_integral_bound decayPositive (by norm_num : (0 : ℝ) ≤ 0)
    (show 0 ≤ remainder by dsimp only [remainder]; positivity) horizonNonnegative
  simp only [zero_mul, zero_add, zero_div, zero_add] at remainderBound
  have remainderAbsorption := scales.reference_multipole_remainder_weighted_seed_absorption source.val frequencyPositive
    (by linarith : 1 ≤ scales.ratio) distancePositive sourceSmall
  refine ⟨actualIntegrable, ?_⟩
  dsimp only at neutralBound momentBound ⊢
  have scaled := mul_le_mul_of_nonneg_left integralBound (by norm_num : (0 : ℝ) ≤ 4)
  have remainderScaled := mul_le_mul_of_nonneg_left remainderBound (by norm_num : (0 : ℝ) ≤ 4)
  change 4 * (∫ elapsed in (0 : ℝ)..horizon, weight elapsed * remainder) ≤ 4 * (remainder / decay) at remainderScaled
  have remainderFinal := remainderScaled.trans (by
    convert remainderAbsorption using 1 <;> dsimp only [remainder, decay] <;> ring)
  dsimp only [neutralCoefficient, momentCoefficient, weight, neutral, moment, decay, field] at scaled remainderFinal
  have sumBounds := add_le_add (add_le_add neutralBound momentBound) remainderFinal
  apply le_trans ?_ (sumBounds.trans_eq (by ring))
  convert scaled using 1 <;> ring

end EulerNonuniqueness.Paper
