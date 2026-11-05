import EulerNonuniqueness.Section6.FourPointVelocityMomentBound
import EulerNonuniqueness.Section6.SourcePacketReferenceUniformWindow
import EulerNonuniqueness.Section6.SourcePacketVelocityWeightedBudget
import EulerNonuniqueness.Section6.PaperReferenceShapeForcing

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 500000

private theorem reference_velocity_scalar_bound
    {circulation length patchRadius omega ratio weight distance neutral deformation seed : ℝ}
    (circulationPositive : 0 < circulation) (lengthPositive : 0 < length)
    (omegaPositive : 0 < omega) (ratioOne : 1 ≤ ratio) (weightLarge : omega ≤ weight)
    (distancePositive : 0 < distance) (distanceOne : distance ≤ 1)
    (neutralNonnegative : 0 ≤ neutral) (deformationNonnegative : 0 ≤ deformation)
    (radiusSmall : patchRadius ^ 2 ≤ length ^ 2)
    (circulationIdentity : circulation = 2 * Real.pi * (ratio * omega) * length ^ 2)
    (seedIdentity : seed = Real.sqrt 3 * circulation ^ 2 / (2 * Real.sqrt 2 * Real.pi ^ 2 * omega ^ 2 * distance ^ 4)) :
    ((circulation / (2 * Real.pi)) * (16 * (2 * neutral * length ^ 2) / distance ^ 2 +
        64 * (4 * length) ^ 2 / distance ^ 3) +
      512 * circulation * patchRadius ^ 2 * deformation / (Real.pi * (distance / 2) ^ 3)) / (weight * distance) ≤
      (1024 / ratio + 32 * neutral + 8192 * deformation) * seed := by
  have ratioPositive : 0 < ratio := zero_lt_one.trans_le ratioOne
  have weightPositive : 0 < weight := omegaPositive.trans_le weightLarge
  let base := circulation ^ 2 / (Real.pi ^ 2 * omega ^ 2 * distance ^ 4)
  let upper := (circulation / (2 * Real.pi)) * (16 * (2 * neutral * length ^ 2) / distance ^ 2 +
    64 * (4 * length) ^ 2 / distance ^ 3) + 512 * circulation * length ^ 2 * deformation / (Real.pi * (distance / 2) ^ 3)
  have upperNonnegative : 0 ≤ upper := by dsimp only [upper]; positivity
  have radiusComparison :
      ((circulation / (2 * Real.pi)) * (16 * (2 * neutral * length ^ 2) / distance ^ 2 +
          64 * (4 * length) ^ 2 / distance ^ 3) +
        512 * circulation * patchRadius ^ 2 * deformation / (Real.pi * (distance / 2) ^ 3)) ≤ upper := by
    dsimp only [upper]
    gcongr
  have weightComparison : weight * distance ≥ omega * distance := mul_le_mul_of_nonneg_right weightLarge distancePositive.le
  have actual := (div_le_div_of_nonneg_right radiusComparison (mul_nonneg weightPositive.le distancePositive.le)).trans
    (div_le_div_of_nonneg_left upperNonnegative (mul_pos omegaPositive distancePositive) weightComparison)
  have identity : upper / (omega * distance) = base * ((8 * neutral * distance + 256 + 2048 * deformation) / ratio) := by
    dsimp only [upper, base]
    rw [circulationIdentity]
    field_simp
    ring
  rw [identity] at actual
  have distanceRatio : distance / ratio ≤ 1 := (div_le_iff₀ ratioPositive).mpr (by simpa only [one_mul] using distanceOne.trans ratioOne)
  have inverseRatio : 1 / ratio ≤ 1 := (div_le_iff₀ ratioPositive).mpr (by simpa only [one_mul] using ratioOne)
  have neutralBound := mul_le_mul_of_nonneg_left distanceRatio (show 0 ≤ 8 * neutral by positivity)
  have deformationBound := mul_le_mul_of_nonneg_left inverseRatio (show 0 ≤ 2048 * deformation by positivity)
  have coefficient : (8 * neutral * distance + 256 + 2048 * deformation) / ratio ≤
      256 / ratio + 8 * neutral + 2048 * deformation := by
    convert add_le_add (add_le_add neutralBound (le_refl (256 / ratio))) deformationBound using 1 <;> ring
  have baseNonnegative : 0 ≤ base := by dsimp only [base]; positivity
  have baseSeed : base ≤ 4 * seed := by
    rw [seedIdentity]
    dsimp only [base]
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have sqrtTwoUpper : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    have sqrtThreeLower : 1 ≤ Real.sqrt 3 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
    have factor : 2 * Real.sqrt 2 ≤ 4 * Real.sqrt 3 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right factor
      (show 0 ≤ circulation ^ 2 * (Real.pi ^ 2 * omega ^ 2 * distance ^ 4) by positivity)]
  apply actual.trans
  have first := mul_le_mul_of_nonneg_left coefficient baseNonnegative
  have second := mul_le_mul_of_nonneg_right baseSeed
    (show 0 ≤ 256 / ratio + 8 * neutral + 2048 * deformation by positivity)
  exact first.trans (second.trans_eq (by ring))

private theorem FinitePatchEvolution.reference_velocity_envelope
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {threshold constant time distance : ℝ}
    (evolution : FinitePatchEvolution scales motion 2) (inside : time ∈ Icc 0 2)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (constantNonnegative : 0 ≤ constant)
    (thresholdSmall : threshold ≤ 1 / 4) (coarse : ReferenceCoarseBounds scales motion threshold constant)
    (source : Fin count) (location : ℂ) (distancePositive : 0 < distance)
    (locationFar : distance ≤ ‖location - quadrupoleCenter motion time source‖)
    (scaleSmall : 8 * scales.length (source.val + 1) ≤ distance)
    (strainSmall : constant * scales.strain ≤ 1)
    (neutralScaleSmall : constant * scales.hessian * scales.length (source.val + 1) ^ 2 * 2 *
      Real.exp (2 * (constant * scales.strain)) ≤ scales.length (source.val + 1))
    (radiusSmall : scales.radius (source.val + 1) ≤ scales.length (source.val + 1))
    (deformationSmall : constant * (scales.omega (source.val + 1))⁻¹ ^ 2 ≤ 1 / 16) :
    ‖biotSavart (quadrupoleDensity scales motion time source) location‖ ≤
      (scales.circulation (source.val + 1) / (2 * Real.pi)) *
        (16 * (2 * (constant * scales.hessian * Real.exp 2) * scales.length (source.val + 1) ^ 2) / distance ^ 2 +
          64 * (4 * scales.length (source.val + 1)) ^ 2 / distance ^ 3) +
        512 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 *
          (constant * (scales.omega (source.val + 1))⁻¹ ^ 2) / (Real.pi * (distance / 2) ^ 3) := by
  have bounds := coarse.2.1 time inside source
  have lengthPositive := scales.length_pos (source.val + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (source.val + 1)
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun index =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun index =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (scales.location_pos _).le _)
  have exponent : Real.exp (constant * scales.strain * time) ≤ Real.exp (2 * (constant * scales.strain)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left inside.2 (mul_nonneg constantNonnegative strainNonnegative)])
  have neutralBound : ‖centroidAsymmetry motion time source‖ ≤
      constant * scales.hessian * scales.length (source.val + 1) ^ 2 * 2 * Real.exp (2 * (constant * scales.strain)) := by
    apply bounds.2.2.2.2.1.trans
    have actual := mul_le_mul (mul_le_mul_of_nonneg_left inside.2
      (show 0 ≤ constant * scales.hessian * scales.length (source.val + 1) ^ 2 by positivity)) exponent
      (Real.exp_pos _).le (by positivity)
    convert actual using 1 <;> ring
  have neutralSmall := neutralBound.trans neutralScaleSmall
  have neutralEnvelope : ‖centroidAsymmetry motion time source‖ ≤
      2 * (constant * scales.hessian * Real.exp 2) * scales.length (source.val + 1) ^ 2 := by
    apply neutralBound.trans
    have exponential := Real.exp_le_exp.mpr (show 2 * (constant * scales.strain) ≤ 2 by linarith)
    have actual := mul_le_mul_of_nonneg_left exponential
      (show 0 ≤ constant * scales.hessian * scales.length (source.val + 1) ^ 2 * 2 by positivity)
    convert actual using 1 <;> ring
  have differencePositive : 0 < diagonalDifference motion time source := by
    have lower := (le_div_iff₀ (sq_pos_of_pos lengthPositive)).mp bounds.2.2.1
    nlinarith
  have differenceUpper : diagonalDifference motion time source ≤ 2 * scales.length (source.val + 1) ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos lengthPositive)).mp bounds.2.2.2.1
  have radialUpper : radialShape motion time source ≤ 1 / 2 := by
    rw [radialShape_eq_unstable_add_stable]
    linarith [(le_abs_self _).trans bounds.1, (le_abs_self _).trans bounds.2.1]
  obtain ⟨positiveBound, negativeBound⟩ := halfDiagonals_norm_le_of_reference_shape
    lengthPositive differencePositive differenceUpper radialUpper
  have centroidBound (patch : Fin 4) : ‖patchCentroid motion time source patch - quadrupoleCenter motion time source‖ ≤
      4 * scales.length (source.val + 1) :=
    (patchCentroid_distance_le_of_halfDiagonals positiveBound negativeBound neutralSmall patch).trans (by linarith)
  have separated (patch : Fin 4) : distance / 2 ≤ ‖location - patchCentroid motion time source patch‖ := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub location (patchCentroid motion time source patch) (quadrupoleCenter motion time source)
    linarith [centroidBound patch]
  have actual := evolution.quadrupole_velocity_moment_bound inside amplitudePositive frequencyPositive ratioPositive source location
    (quadrupoleCenter motion time source) bounds.2.2.2.2.2 (by positivity) deformationSmall
    (show 0 < distance / 2 by positivity) (by linarith) separated (by positivity : 0 ≤ 4 * scales.length (source.val + 1))
    (distancePositive.trans_le locationFar) (by linarith) centroidBound
  have moment := centroid_fourPointSignedMoment motion time source
  rw [moment, norm_mul] at actual
  norm_num only [Complex.norm_ofNat] at actual
  apply actual.trans
  have firstTerm := div_le_div_of_nonneg_left (show 0 ≤ 4 * (4 * ‖centroidAsymmetry motion time source‖) by positivity)
    (sq_pos_of_pos distancePositive) (pow_le_pow_left₀ distancePositive.le locationFar 2)
  have secondTerm := div_le_div_of_nonneg_left (show 0 ≤ 64 * (4 * scales.length (source.val + 1)) ^ 2 by positivity)
    (pow_pos distancePositive 3) (pow_le_pow_left₀ distancePositive.le locationFar 3)
  have neutralComparison := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left neutralEnvelope
    (show 0 ≤ (16 : ℝ) by norm_num)) (sq_nonneg distance)
  have first : 4 * (4 * ‖centroidAsymmetry motion time source‖) / ‖location - quadrupoleCenter motion time source‖ ^ 2 ≤
      16 * (2 * (constant * scales.hessian * Real.exp 2) * scales.length (source.val + 1) ^ 2) / distance ^ 2 := by
    have normalized : 4 * (4 * ‖centroidAsymmetry motion time source‖) / distance ^ 2 ≤
        16 * (2 * (constant * scales.hessian * Real.exp 2) * scales.length (source.val + 1) ^ 2) / distance ^ 2 := by
      convert neutralComparison using 1 <;> ring
    exact firstTerm.trans normalized
  exact add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add first secondTerm)
    (div_nonneg circulationPositive.le (by positivity))) _

theorem exists_uniform_reference_velocity_window_seed_budget :
    ∃ universalConstant ≥ (0 : ℝ), ∀ scales : Scales, 0 < scales.amplitude → 8192 ≤ scales.ratio → 0 < scales.alpha →
    ∀ constant separationFactor tolerance : ℝ, 0 ≤ constant → 0 < separationFactor → 0 < tolerance →
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) {threshold start horizon distance : ℝ},
    let changed : Scales := {scales with frequency := frequency}
    (∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * changed.amplitude * changed.omega (index.val + 1) ^ 4) →
    FinitePatchEvolution changed family.patchMotion 2 → threshold ≤ 1 / 4 →
    ReferenceCoarseBounds changed family.patchMotion threshold constant →
    0 ≤ start → 0 ≤ horizon → start + horizon ≤ 2 →
    ∀ source : Fin count, ∀ location : ℝ → ℂ, Measurable location → 0 < distance → distance ≤ 1 →
    separationFactor * changed.location (source.val + 1) ≤ distance →
    (∀ elapsed ∈ Icc 0 horizon,
      distance ≤ ‖location elapsed - quadrupoleCenter family.patchMotion (start + elapsed) source‖) →
    let decay := 2 * Real.sqrt 2 * changed.omega source.val
    let field := fun elapsed => biotSavart (quadrupoleDensity changed family.patchMotion (start + elapsed) source) (location elapsed)
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * ‖field elapsed‖ / distance) volume 0 horizon ∧
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * ‖field elapsed‖ / distance) ≤
      (universalConstant / scales.ratio + tolerance) * (Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * distance ^ 4)) := by
  refine ⟨1024, by norm_num, ?_⟩
  intro scales amplitudePositive ratioLarge alphaPositive constant separationFactor tolerance constantNonnegative factorPositive tolerancePositive
  have ratioBound : 2 ≤ scales.ratio := by linarith
  have strainLimit : Tendsto (fun frequency : ℝ => constant * ({scales with frequency := frequency}).strain) atTop (𝓝 0) := by
    simpa only [mul_zero] using (scales.strain_tendsto_zero ratioBound alphaPositive).const_mul constant
  have neutralLimit : Tendsto (fun frequency : ℝ => constant * ({scales with frequency := frequency}).hessian * Real.exp 2) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using ((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul constant).mul_const (Real.exp 2)
  have deformationLimit : Tendsto (fun frequency : ℝ => constant * frequency⁻¹ ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      ((tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).pow 2).const_mul constant
  filter_upwards [scales.eventually_reference_source_packet_budgets amplitudePositive ratioBound alphaPositive constantNonnegative factorPositive,
    strainLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    neutralLimit.eventually (eventually_lt_nhds (show 0 < tolerance / 64 by positivity)),
    deformationLimit.eventually (eventually_lt_nhds (show 0 < tolerance / 16384 by positivity))]
    with frequency budgets strainSmall neutralSmall deformationSmall
  intro count family threshold start horizon distance
  dsimp only
  intro densities evolution thresholdSmall coarse startNonnegative horizonNonnegative windowBound source location locationMeasurable
    distancePositive distanceOne separation locationFar
  let changed : Scales := {scales with frequency := frequency}
  obtain ⟨frequencyPositive, _, sourceSmall, _, _, _, neutralScaleSmall, radiusSmall, _, deformationBound⟩ :=
    budgets source.val distance separation distanceOne
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith
  have lengthPositive := changed.length_pos (source.val + 1)
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive source.val
  have sourcePositive := changed.omega_pos frequencyPositive ratioPositive (source.val + 1)
  have circulationPositive := changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun index =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
  let decay := 2 * Real.sqrt 2 * changed.omega source.val
  let deformation := constant * (changed.omega (source.val + 1))⁻¹ ^ 2
  let neutral := constant * changed.hessian * Real.exp 2
  let envelope := (changed.circulation (source.val + 1) / (2 * Real.pi)) *
    (16 * (2 * neutral * changed.length (source.val + 1) ^ 2) / distance ^ 2 +
      64 * (4 * changed.length (source.val + 1)) ^ 2 / distance ^ 3) +
    512 * changed.circulation (source.val + 1) * changed.radius (source.val + 1) ^ 2 * deformation /
      (Real.pi * (distance / 2) ^ 3)
  let field := fun elapsed => biotSavart (quadrupoleDensity changed family.patchMotion (start + elapsed) source) (location elapsed)
  let seed := Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
    (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * distance ^ 4)
  have decayPositive : 0 < decay := by dsimp only [decay]; positivity
  have neutralNonnegative : 0 ≤ neutral := by dsimp only [neutral]; positivity
  have deformationNonnegative : 0 ≤ deformation := by dsimp only [deformation]; positivity
  have envelopeNonnegative : 0 ≤ envelope := by dsimp only [envelope]; positivity
  have scaleSmall : 8 * changed.length (source.val + 1) ≤ distance := by
    have actual := (div_le_iff₀ distancePositive).mp sourceSmall
    linarith
  have pointwise (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : ‖field elapsed‖ ≤ envelope :=
    evolution.reference_velocity_envelope (time := start + elapsed) ⟨by linarith [inside.1], by linarith [inside.2]⟩ amplitudePositive frequencyPositive
      ratioPositive constantNonnegative thresholdSmall coarse source (location elapsed) distancePositive (locationFar elapsed inside)
      scaleSmall strainSmall.le neutralScaleSmall radiusSmall deformationBound
  have joint := measurable_biotSavart_of_measurable_vorticity (Parameter := ℝ)
    (vorticity := fun time => quadrupoleDensity changed family.patchMotion time source)
    (family.measurable_quadrupoleDensity changed densities source)
  have timeMeasurable : Measurable (fun elapsed : ℝ => start + elapsed) := measurable_const.add measurable_id
  have fieldMeasurable : Measurable field := by
    simpa only [field, Function.comp_def] using joint.comp (timeMeasurable.prodMk locationMeasurable)
  have exponentialContinuous : Continuous (fun elapsed : ℝ => Real.exp (-decay * elapsed)) := by fun_prop
  have majorantIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * envelope) volume 0 horizon :=
    (exponentialContinuous.mul continuous_const).intervalIntegrable (μ := volume) 0 horizon
  have actualIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * ‖field elapsed‖) volume 0 horizon :=
    (show IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * envelope) volume 0 horizon from majorantIntegrable).mono_fun'
      (exponentialContinuous.measurable.mul fieldMeasurable.norm).aestronglyMeasurable.restrict (by
        rw [uIoc_of_le horizonNonnegative]
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with elapsed inside
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
        exact mul_le_mul_of_nonneg_left (pointwise elapsed ⟨inside.1.le, inside.2⟩) (Real.exp_pos _).le)
  have integralBound := intervalIntegral.integral_mono_on (μ := volume) horizonNonnegative actualIntegrable
    (show IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * envelope) volume 0 horizon from majorantIntegrable)
    (fun elapsed inside => mul_le_mul_of_nonneg_left (pointwise elapsed inside) (Real.exp_pos _).le)
  have constantBound := laplace_affine_integral_bound (slope := 0) (constant := envelope)
    decayPositive (by norm_num) envelopeNonnegative horizonNonnegative
  simp only [zero_mul, zero_add, zero_div] at constantBound
  have normalized := div_le_div_of_nonneg_right (integralBound.trans constantBound) distancePositive.le
  have deformationSmallActual : deformation ≤ tolerance / 16384 := by
    have sourceLarge : frequency ≤ changed.omega (source.val + 1) :=
      changed.omega_ge_frequency frequencyPositive (by dsimp only [changed]; linarith) _
    have inverse := inv_anti₀ frequencyPositive sourceLarge
    have squared := pow_le_pow_left₀ (inv_nonneg.mpr sourcePositive.le) inverse 2
    exact (mul_le_mul_of_nonneg_left squared constantNonnegative).trans deformationSmall.le
  have decayLarge : changed.omega source.val ≤ decay := by
    have sqrtLower : 1 ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    dsimp only [decay]
    nlinarith [mul_le_mul_of_nonneg_right sqrtLower omegaPositive.le]
  have circulationIdentity : changed.circulation (source.val + 1) =
      2 * Real.pi * (changed.ratio * changed.omega source.val) * changed.length (source.val + 1) ^ 2 := by
    dsimp only [Scales.circulation, Scales.omega]
    rw [pow_succ]
    ring
  have scalar := reference_velocity_scalar_bound circulationPositive lengthPositive omegaPositive
    (show 1 ≤ changed.ratio by dsimp only [changed]; linarith) decayLarge distancePositive distanceOne neutralNonnegative
    deformationNonnegative (pow_le_pow_left₀ (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le radiusSmall 2)
    circulationIdentity (by rfl : seed = _)
  have normalizedBound : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * ‖field elapsed‖) / distance ≤
      (1024 / changed.ratio + 32 * neutral + 8192 * deformation) * seed := by
    apply normalized.trans
    convert scalar using 1 <;> dsimp only [envelope] <;> ring
  have seedNonnegative : 0 ≤ seed := by dsimp only [seed]; positivity
  have smallCosts : 32 * neutral + 8192 * deformation ≤ tolerance := by
    have first : neutral ≤ tolerance / 64 := neutralSmall.le
    nlinarith only [first, deformationSmallActual]
  refine ⟨actualIntegrable.div_const distance, ?_⟩
  rw [intervalIntegral.integral_div]
  exact normalizedBound.trans (mul_le_mul_of_nonneg_right (by dsimp only [changed]; linarith) seedNonnegative)

end EulerNonuniqueness.Paper
