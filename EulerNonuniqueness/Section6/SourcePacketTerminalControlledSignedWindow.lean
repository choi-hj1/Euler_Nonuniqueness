import EulerNonuniqueness.Section6.SourcePacketActualRetainedSignedWindow
import EulerNonuniqueness.Section5.CascadeInitialSeparation
import EulerNonuniqueness.Section5.CascadeMaterialInitialExtent
import EulerNonuniqueness.Section5.CascadeBlockExtentCentroids
import EulerNonuniqueness.Section5.CascadeGeometricScaleSmallness
import EulerNonuniqueness.Section6.PhysicalOutgoingData
import EulerNonuniqueness.Section6.NegativeLabelBridge

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private theorem terminal_outgoing_initial_data_at_error (orbit : SeparatingOrbit) (sectionTime initialError : ℝ)
    (errorNonnegative : 0 ≤ initialError) (errorSmall : initialError ≤ 1 / 64)
    (radiusLarge : 512 ≤ separationRadius orbit sectionTime)
    (separationClose : ‖orbit.positive sectionTime + orbit.negative sectionTime -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ initialError / 2)
    (outgoing : (7 / 8 : ℝ) * separationRadius orbit sectionTime ≤
      (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
        (orbit.positive sectionTime - orbit.negative sectionTime)).re) :
    ∀ {count : ℕ} {scales : Scales} {horizon : ℝ} {dipoleAngle : ℕ → ℝ}
      {reference alternative : PatchMotion count},
    FinitePatchEvolution scales alternative horizon → 0 ≤ horizon →
    0 < scales.amplitude → 0 < scales.frequency → 0 < scales.ratio →
    CascadeInitialDisks scales orbit sectionTime dipoleAngle reference alternative →
    ∀ index : Fin count, index.val + 1 = count →
    let positions := relabelNegativePoints (fun patch => patchCentroid alternative 0 index patch)
    let direction := Complex.exp (Complex.I * (dipoleAngle count - orbit.limitingDipoleAngle : ℝ)) *
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))
    ‖positions 0 - positions 2 - (scales.length count : ℂ) * direction‖ ≤ initialError * scales.length count ∧
      ‖positions 1 - positions 3 - (scales.length count : ℂ) * (-direction)‖ ≤ initialError * scales.length count ∧
      (3 / 4 : ℝ) * scales.length count * separationRadius orbit sectionTime ≤
        (Complex.I * star direction * ((positions 0 + positions 2) / 2 -
          (positions 1 + positions 3) / 2)).re ∧
      ‖(positions 0 + positions 2) / 2 - (positions 1 + positions 3) / 2‖ ≤
        (5 / 4 : ℝ) * scales.length count * separationRadius orbit sectionTime := by
  intro count scales horizon dipoleAngle reference alternative evolution horizonNonnegative amplitudePositive
    frequencyPositive ratioPositive initial index last
  let positions := relabelNegativePoints (fun patch => patchCentroid alternative 0 index patch)
  let rotation := Complex.exp (Complex.I * (dipoleAngle count - orbit.limitingDipoleAngle : ℝ))
  have positionsIdentity : positions = fun target => (scales.location count : ℂ) +
      (scales.length count : ℂ) * rotation *
        centrallySymmetricFourPoint (orbit.positive sectionTime) (-orbit.negative sectionTime) target := by
    funext target
    dsimp only [positions, relabelNegativePoints]
    rw [evolution.cascade_terminal_initial_centroid horizonNonnegative amplitudePositive frequencyPositive
      ratioPositive initial index last, separatingInitialCenter_eq_physical_orbit]
    simp [physicalSeparatingPointOrbit, rotation, negativeLabelSwap]
  have close : ‖positions - (fun target => (scales.location count : ℂ) +
      (scales.length count : ℂ) * rotation *
        centrallySymmetricFourPoint (orbit.positive sectionTime) (-orbit.negative sectionTime) target)‖ ≤
      initialError * scales.length count / 4 := by
    rw [positionsIdentity, sub_self, norm_zero]
    exact div_nonneg (mul_nonneg errorNonnegative (scales.length_pos count).le) (by norm_num)
  have result := physical_outgoing_initial_data (positive := orbit.positive sectionTime)
    (negative := orbit.negative sectionTime) (direction := Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ)))
    (rotation := rotation) (center := (scales.location count : ℂ)) (positions := positions)
    (length := scales.length count) (error := initialError) (scales.length_pos count) errorNonnegative errorSmall
    (by simp [Complex.norm_exp, Complex.mul_re]) (by simp [rotation, Complex.norm_exp, Complex.mul_re])
    radiusLarge separationClose outgoing close
  simpa only [positions, rotation, separationRadius] using result


theorem exists_actual_terminal_controlled_signed_window (orbit : SeparatingOrbit) (sectionTime initialError : ℝ)
    (errorNonnegative : 0 ≤ initialError) (errorSmall : initialError ≤ 1 / 64)
    (radiusLarge : 2048 ≤ separationRadius orbit sectionTime)
    (separationClose : ‖orbit.positive sectionTime + orbit.negative sectionTime -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ initialError / 2)
    (outgoing : (7 / 8 : ℝ) * separationRadius orbit sectionTime ≤
      (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
        (orbit.positive sectionTime - orbit.negative sectionTime)).re) :
    ∃ extent ≥ (4 : ℝ), ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
    ∀ tolerance : ℝ, 0 < tolerance → tolerance ≤ 1 / 8 →
    20 * initialError + 83200 / (separationRadius orbit sectionTime) ^ 2 ≤
      min (tolerance / 4) 1 / 5120 →
    ∀ scales : Scales, 0 < scales.amplitude → 0 < scales.alpha →
    max 2 (65536 / tolerance) ≤ scales.ratio →
    12 * separationRadius orbit sectionTime ≤ (tolerance / 2) * scales.ratio →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ factor scaleRoot boundaryConstant : ℝ,
    0 < factor → factor ≤ 1 / 8 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count,
    receiver.val + 1 = source.val → source.val + 1 = count →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let omega := changed.omega (receiver.val + 1)
    let lambda := 2 * Real.sqrt 2 * omega
    let seed := changed.seed (receiver.val + 1)
    let frozen : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
    let residual := 4 * Complex.arg frozen - 2 * phase (receiver.val + 1) -
      2 * dipoleAngle count + Real.arctan (1 / Real.sqrt 2) - Real.pi
    let input := fun time => (relativeBlockSourceShapeInput changed motion prepared.reference receiver source time).1
    ContinuousOn input (Icc 0 path.stop) ∧
    (∀ patch : Fin 4, motion.domain 0 source patch ⊆
      closedBall (quadrupoleCenter motion 0 source) (extent * changed.length (source.val + 1))) ∧
    (∫ time in (0 : ℝ)..0, Real.exp (-lambda * time) * input time) = 0 ∧
    ∀ horizon : ℝ, 0 ≤ horizon → horizon ≤ path.stop →
      IntervalIntegrable (fun time => Real.exp (-lambda * time) * input time) volume 0 horizon ∧
      |(∫ time in (0 : ℝ)..horizon, Real.exp (-lambda * time) * input time) / seed - Real.cos residual| ≤
        tolerance + 17 * Real.exp (-(3 * lambda / 4) * horizon) ∧
      Real.cos residual - tolerance - 17 * Real.exp (-(3 * lambda / 4) * horizon) ≤
        (∫ time in (0 : ℝ)..horizon, Real.exp (-lambda * time) * input time) / seed := by
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, windows⟩ := exists_actual_retained_signed_window
  let centroidExtent := max 3 (max ‖orbit.positive sectionTime‖ ‖orbit.negative sectionTime‖)
  let extent := centroidExtent + 1
  have centroidThree : 3 ≤ centroidExtent := le_max_left _ _
  have positiveBound : ‖orbit.positive sectionTime‖ ≤ centroidExtent :=
    (le_max_left _ _).trans (le_max_right _ _)
  have negativeBound : ‖orbit.negative sectionTime‖ ≤ centroidExtent :=
    (le_max_right _ _).trans (le_max_right _ _)
  have extentFour : 4 ≤ extent := by dsimp only [extent]; linarith only [centroidThree]
  refine ⟨extent, extentFour, thresholdMax, thresholdPositive, thresholdEighth, ?_⟩
  intro tolerance tolerancePositive toleranceEighth numericBudget scales amplitudePositive alphaPositive ratioLarge ratioBudget
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound factor scaleRoot boundaryConstant
    factorPositive factorSmall rootOne boundaryOne
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  filter_upwards [windows tolerance tolerancePositive toleranceEighth scales amplitudePositive alphaPositive ratioLarge
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime factor scaleRoot
      boundaryConstant extent initialError factorPositive factorSmall rootOne boundaryOne
      ((by norm_num : (0 : ℝ) < 4).trans_le extentFour) errorSmall,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num),
    eventually_gt_atTop (max 0 (16 * separationRadius orbit sectionTime))]
    with frequency windowEstimate geometry frequencyLarge
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent last
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let length := changed.length (source.val + 1)
  let omega := changed.omega (receiver.val + 1)
  let lambda := 2 * Real.sqrt 2 * omega
  let seed := changed.seed (receiver.val + 1)
  let frozen : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  let residual := 4 * Complex.arg frozen - 2 * phase (receiver.val + 1) -
    2 * dipoleAngle count + Real.arctan (1 / Real.sqrt 2) - Real.pi
  let input := fun time => (relativeBlockSourceShapeInput changed motion prepared.reference receiver source time).1
  have frequencyPositive : 0 < changed.frequency := (le_max_left _ _).trans_lt frequencyLarge
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have lengthPositive : 0 < length := changed.length_pos _
  have initial := terminal_outgoing_initial_data_at_error orbit sectionTime initialError errorNonnegative errorSmall
    ((by norm_num : (512 : ℝ) ≤ 2048).trans radiusLarge) separationClose outgoing
    path.evolution path.stopPositive.le amplitudePositive frequencyPositive ratioPositive prepared.commonInitial source last
  dsimp only at initial
  let direction := Complex.exp (Complex.I * (dipoleAngle count - orbit.limitingDipoleAngle : ℝ)) *
    Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))
  have directionIdentity : direction = Complex.exp (Complex.I * (dipoleAngle count : ℂ)) := by
    dsimp only [direction]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have firstInitial : ‖firstDipoleSeparation motion 0 source -
      (length : ℂ) * Complex.exp (Complex.I * (dipoleAngle count : ℂ))‖ ≤ initialError * length := by
    simpa [firstDipoleSeparation, relabelNegativePoints, negativeLabelSwap, Equiv.swap_apply_def,
      ← directionIdentity, direction, changed, last, length, motion] using initial.1
  have secondInitial : ‖secondDipoleSeparation motion 0 source -
      (length : ℂ) * (-Complex.exp (Complex.I * (dipoleAngle count : ℂ)))‖ ≤ initialError * length := by
    simpa [secondDipoleSeparation, relabelNegativePoints, negativeLabelSwap, Equiv.swap_apply_def,
      ← directionIdentity, direction, changed, last, length, motion] using initial.2.1
  have projectionInitial : (3 / 4 : ℝ) * length * separationRadius orbit sectionTime ≤
      (Complex.I * star (Complex.exp (Complex.I * (dipoleAngle count : ℂ))) *
        (firstDipoleCenter motion 0 source - secondDipoleCenter motion 0 source)).re := by
    simpa [firstDipoleCenter, secondDipoleCenter, relabelNegativePoints, negativeLabelSwap,
      Equiv.swap_apply_def, ← directionIdentity, direction, changed, last, length, motion] using initial.2.2.1
  have upperInitial : ‖firstDipoleCenter motion 0 source - secondDipoleCenter motion 0 source‖ ≤
      (5 / 4 : ℝ) * length * separationRadius orbit sectionTime := by
    simpa [firstDipoleCenter, secondDipoleCenter, relabelNegativePoints, negativeLabelSwap,
      Equiv.swap_apply_def, changed, last, length, motion] using initial.2.2.2
  have sourceSmall : separationRadius orbit sectionTime ≤ changed.omega (source.val + 1) / 16 := by
    have bound := (le_max_right _ _).trans_lt frequencyLarge
    have omegaBound := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith only [ratioBound]) (source.val + 1)
    change frequency ≤ changed.omega (source.val + 1) at omegaBound
    linarith only [bound, omegaBound]
  have radiusSmall : 2 * changed.radius (source.val + 1) ≤ length := by
    have bound := (geometry (source.val + 1)).2.1
    change changed.radius (source.val + 1) ≤ 1 * length / 1000 at bound
    linarith only [bound, lengthPositive]
  have initialExtent := prepared.initial_extent_bound
    (thresholdBound.trans (thresholdEighth.trans (by norm_num))) centroidThree positiveBound negativeBound source
  have domainInitial (patch : Fin 4) : motion.domain 0 source patch ⊆
      closedBall (quadrupoleCenter motion 0 source) (extent * length) := by
    intro position member
    have centroid := (norm_le_pi_norm (prepared.trajectory.blockExtentVector source 0) patch).trans initialExtent
    rw [prepared.trajectory.blockExtentVector_eq_centroid_offset (fun _ => rfl)
      (by constructor <;> norm_num) source patch] at centroid
    have domain := prepared.trajectory.domain_subset_centroid_ball changed prepared.radiusIdentity (fun _ => rfl)
      (by constructor <;> norm_num) source patch member
    rw [mem_closedBall, dist_eq_norm] at domain ⊢
    have triangle := norm_sub_le_norm_sub_add_norm_sub position (patchCentroid motion 0 source patch)
      (quadrupoleCenter motion 0 source)
    dsimp only [extent]
    nlinarith only [triangle, centroid, domain, radiusSmall]
  have prefixDomains (time : ℝ) (inside : time ∈ Icc (0 : ℝ) 0) (patch : Fin 4) :
      motion.domain time source patch ⊆ closedBall (quadrupoleCenter motion time source) (extent * length) := by
    have zero : time = 0 := le_antisymm inside.2 inside.1
    subst time
    exact domainInitial patch
  have actual := windowEstimate count phase dipoleAngle prepared path receiver source adjacent
    0 ⟨le_rfl, path.stopPositive.le⟩ (separationRadius orbit sectionTime) (dipoleAngle count)
    radiusLarge sourceSmall ratioBudget numericBudget firstInitial secondInitial projectionInitial upperInitial prefixDomains
  dsimp only at actual
  simp only [← prepared.referenceIdentity] at actual
  obtain ⟨inputContinuous, _, _, _, _, _, _, actualWindows⟩ := actual
  refine ⟨inputContinuous, domainInitial, intervalIntegral.integral_same, ?_⟩
  intro horizon horizonNonnegative horizonBound
  obtain ⟨integrable, _, _, _, estimate⟩ := actualWindows horizon horizonNonnegative (by simpa only [zero_add] using horizonBound)
  have normalizedBound : |(∫ time in (0 : ℝ)..horizon, Real.exp (-lambda * time) * input time) / seed - Real.cos residual| ≤
      tolerance + 17 * Real.exp (-(3 * lambda / 4) * horizon) := by
    simpa only [mul_zero, sub_zero, Real.exp_zero, one_mul, zero_add, intervalIntegral.integral_same,
      abs_zero, mul_zero, zero_div, add_zero] using estimate
  refine ⟨by simpa only [zero_add] using integrable, normalizedBound, ?_⟩
  have lower := (abs_le.mp normalizedBound).1
  linarith only [lower]

end EulerNonuniqueness.Paper
