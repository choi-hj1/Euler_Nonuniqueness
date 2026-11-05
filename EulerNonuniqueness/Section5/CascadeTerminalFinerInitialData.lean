import EulerNonuniqueness.Section5.CascadeInitialSharpState
import EulerNonuniqueness.Section5.CascadeTerminalSectionData
import EulerNonuniqueness.Section5.CascadeOutgoingInternalGap

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
open EulerNonuniqueness.Section6
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem eventually_actual_terminal_finer_initial_data (orbit : SeparatingOrbit) (sectionTime initialError : ℝ)
    (_errorNonnegative : 0 ≤ initialError) (errorSmall : initialError ≤ 1 / 64)
    (radiusLarge : 2048 ≤ separationRadius orbit sectionTime)
    (separationClose : ‖orbit.positive sectionTime + orbit.negative sectionTime -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ initialError / 2)
    (outgoing : (7 / 8 : ℝ) * separationRadius orbit sectionTime ≤
      (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
        (orbit.positive sectionTime - orbit.negative sectionTime)).re) :
    let modelBound := max 3 (max ‖orbit.positive sectionTime‖ ‖orbit.negative sectionTime‖)
    let extent := max 4 (modelBound + 1)
    let magnitude := modelBound + 2
    ∀ scales : Scales, 0 < scales.amplitude → 128 ≤ scales.ratio → 0 < scales.alpha →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant rawCap : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, threshold ≤ 1 / 2 →
    ∀ index source : Fin count, index.val + 1 = source.val → source.val + 1 = count →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let direction := Complex.exp (Complex.I * (dipoleAngle count : ℂ))
    (4 ≤ extent ∧ 0 ≤ magnitude) ∧
    (∀ other : Fin count, index.val < other.val → other = source) ∧
    (∀ other : Fin count, index.val < other.val →
      let length := changed.length (other.val + 1)
      0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ path.stop ∧ 512 ≤ separationRadius orbit sectionTime ∧
      separationRadius orbit sectionTime ≤ changed.omega (other.val + 1) / 16 ∧ ‖direction‖ = 1 ∧
      ‖firstDipoleSeparation motion 0 other - (length : ℂ) * direction‖ ≤ length / 64 ∧
      ‖secondDipoleSeparation motion 0 other - (length : ℂ) * (-direction)‖ ≤ length / 64 ∧
      (3 / 4 : ℝ) * length * separationRadius orbit sectionTime ≤
        (Complex.I * star direction * (firstDipoleCenter motion 0 other - secondDipoleCenter motion 0 other)).re ∧
      ‖firstDipoleCenter motion 0 other - secondDipoleCenter motion 0 other‖ ≤
        (5 / 4 : ℝ) * length * separationRadius orbit sectionTime) ∧
    (∀ other : Fin count, index.val < other.val → ∀ time ∈ Icc (0 : ℝ) 0,
      (∀ patch : Fin 4, ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time other patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time other‖ ≤
          extent * changed.length (other.val + 1)) ∧
      (∀ patch : Fin 4, ‖patchCentroid motion time other patch - quadrupoleCenter motion time other‖ ≤
          extent * changed.length (other.val + 1))) ∧
    (∀ other : Fin count, index.val < other.val → ∀ time ∈ Icc (0 : ℝ) 0,
      prepared.rawSourceCenteredState time other +
        ‖relativeNormalizedFirstMoment changed motion prepared.reference other time‖ +
        ‖quadrupoleCenter motion time other - quadrupoleCenter prepared.reference time other‖ /
          changed.location (other.val + 1) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time other patch ≤
        magnitude * Real.exp ((1 / 16 : ℝ) * changed.omega (other.val + 1) * (time - 0))) ∧
    (∀ other : Fin count, index.val < other.val → ∀ time ∈ Icc (0 : ℝ) 0, ∀ patch,
      motion.domain time other patch ⊆ Metric.closedBall (quadrupoleCenter motion time other)
        (extent * changed.length (other.val + 1))) ∧
    (∀ other : Fin count, index.val < other.val →
      2 * (2 * Real.sqrt 2 * changed.omega (index.val + 1)) ≤ (1 / 16 : ℝ) * changed.omega (other.val + 1)) ∧
    |(0 : ℝ) - changed.predictedTime sectionTime count (index.val + 2)| ≤ 0 / changed.omega (index.val + 2) ∧
    (∀ other : Fin count, index.val < other.val →
      |(0 : ℝ) - changed.predictedTime sectionTime count (other.val + 1)| ≤ 0 / changed.omega (other.val + 1)) := by
  dsimp only
  let modelBound := max 3 (max ‖orbit.positive sectionTime‖ ‖orbit.negative sectionTime‖)
  let extent := max 4 (modelBound + 1)
  let magnitude := modelBound + 2
  have boundThree : 3 ≤ modelBound := le_max_left _ _
  have positiveBound : ‖orbit.positive sectionTime‖ ≤ modelBound :=
    (le_max_left _ _).trans (le_max_right _ _)
  have negativeBound : ‖orbit.negative sectionTime‖ ≤ modelBound :=
    (le_max_right _ _).trans (le_max_right _ _)
  have extentFour : 4 ≤ extent := le_max_left _ _
  have boundExtent : modelBound + 1 ≤ extent := le_max_right _ _
  have extentOne : 1 ≤ extent := by linarith
  have magnitudeNonnegative : 0 ≤ magnitude := by dsimp only [magnitude]; linarith
  have distanceNonnegative : 0 ≤ separationRadius orbit sectionTime := by linarith
  intro scales amplitudePositive ratioLarge alphaPositive
  have ratioBound : 2 ≤ scales.ratio := (by norm_num : (2 : ℝ) ≤ 128).trans ratioLarge
  filter_upwards [scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (max 1 (16 * separationRadius orbit sectionTime))]
    with frequency geometry frequencyLarge
  intro count phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant rawCap prepared path
    thresholdSmall index source adjacent terminal
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  have frequencyOne : 1 ≤ frequency := (le_max_left _ _).trans frequencyLarge
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have finerEq (other : Fin count) (finer : index.val < other.val) : other = source := by
    apply Fin.ext
    omega
  have sourceLarge : separationRadius orbit sectionTime ≤ changed.omega (source.val + 1) / 16 := by
    have omegaBound := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) (source.val + 1)
    have bound := (le_max_right _ _).trans frequencyLarge
    change frequency ≤ changed.omega (source.val + 1) at omegaBound
    linarith
  have initial := cascade_terminal_outgoing_initial_data_of_section orbit sectionTime
    ((by norm_num : (512 : ℝ) ≤ 2048).trans radiusLarge) (by linarith only [separationClose, errorSmall]) outgoing
    path.evolution path.stopPositive.le amplitudePositive frequencyPositive ratioPositive prepared.commonInitial source terminal
  dsimp only at initial
  let direction := Complex.exp (Complex.I * (dipoleAngle count : ℂ))
  have directionIdentity : direction = Complex.exp (Complex.I * (dipoleAngle count - orbit.limitingDipoleAngle : ℝ)) *
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ)) := by
    dsimp only [direction]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have directionNorm : ‖direction‖ = 1 := by simp [direction, norm_mul, Complex.norm_exp, Complex.mul_re]
  have firstInitial : ‖firstDipoleSeparation motion 0 source -
      (changed.length (source.val + 1) : ℂ) * direction‖ ≤ changed.length (source.val + 1) / 64 := by
    simpa [firstDipoleSeparation, relabelNegativePoints, negativeLabelSwap, Equiv.swap_apply_def,
      directionIdentity, changed, terminal, motion] using initial.1
  have secondInitial : ‖secondDipoleSeparation motion 0 source -
      (changed.length (source.val + 1) : ℂ) * (-direction)‖ ≤ changed.length (source.val + 1) / 64 := by
    simpa [secondDipoleSeparation, relabelNegativePoints, negativeLabelSwap, Equiv.swap_apply_def,
      directionIdentity, changed, terminal, motion] using initial.2.1
  have projectionInitial : (3 / 4 : ℝ) * changed.length (source.val + 1) * separationRadius orbit sectionTime ≤
      (Complex.I * star direction * (firstDipoleCenter motion 0 source - secondDipoleCenter motion 0 source)).re := by
    simpa [firstDipoleCenter, secondDipoleCenter, relabelNegativePoints, negativeLabelSwap,
      Equiv.swap_apply_def, directionIdentity, changed, terminal, motion] using initial.2.2.1
  have upperInitial : ‖firstDipoleCenter motion 0 source - secondDipoleCenter motion 0 source‖ ≤
      (5 / 4 : ℝ) * changed.length (source.val + 1) * separationRadius orbit sectionTime := by
    simpa [firstDipoleCenter, secondDipoleCenter, relabelNegativePoints, negativeLabelSwap,
      Equiv.swap_apply_def, changed, terminal, motion] using initial.2.2.2
  have actualExtents := prepared.toCascadeMaterialPreparedPair.initial_extent_bound
    thresholdSmall boundThree positiveBound negativeBound source
  have actualExtent (patch : Fin 4) : ‖patchCentroid motion 0 source patch - quadrupoleCenter motion 0 source‖ ≤
      modelBound * changed.length (source.val + 1) := by
    have bound := (norm_le_pi_norm (prepared.trajectory.blockExtentVector source 0) patch).trans actualExtents
    rw [prepared.trajectory.blockExtentVector_eq_centroid_offset (fun _ => rfl)
      (by constructor <;> norm_num) source patch] at bound
    exact bound
  have referenceData := prepared.referenceWitness.evolution.reference_initial_center_and_asymmetry
    (by norm_num : (0 : ℝ) ≤ 2) amplitudePositive frequencyPositive ratioPositive prepared.referenceWitness.initial source
  have referenceExtent (patch : Fin 4) :
      ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion 0 source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion 0 source‖ ≤
          2 * changed.length (source.val + 1) := by
    rw [referenceData.1, prepared.referenceWitness.evolution.reference_initial_centroid
      (by norm_num : (0 : ℝ) ≤ 2) amplitudePositive frequencyPositive ratioPositive prepared.referenceWitness.initial source patch]
    exact initialDiskCenter_offset_bound changed _ _ _
      ((prepared.referenceWitness.initial source).1.trans thresholdSmall) patch
  have domains (patch : Fin 4) : motion.domain 0 source patch ⊆
      Metric.closedBall (quadrupoleCenter motion 0 source) (extent * changed.length (source.val + 1)) := by
    intro position member
    have domain := prepared.trajectory.domain_subset_centroid_ball changed prepared.radiusIdentity (fun _ => rfl)
      (by constructor <;> norm_num) source patch member
    rw [Metric.mem_closedBall, dist_eq_norm] at domain ⊢
    have triangle := norm_sub_le_norm_sub_add_norm_sub position (patchCentroid motion 0 source patch)
      (quadrupoleCenter motion 0 source)
    have radiusBound := (geometry (source.val + 1)).2.1
    change changed.radius (source.val + 1) ≤ 1 * changed.length (source.val + 1) / 1000 at radiusBound
    change ‖position - patchCentroid motion 0 source patch‖ ≤ 2 * changed.radius (source.val + 1) at domain
    have lengthPositive := changed.length_pos (source.val + 1)
    nlinarith only [triangle, actualExtent patch, domain, radiusBound, lengthPositive,
      mul_le_mul_of_nonneg_right boundExtent lengthPositive.le]
  have sharp := prepared.initial_sharp_state_bound path amplitudePositive frequencyPositive ratioPositive
    thresholdSmall boundThree positiveBound negativeBound source
  have sourceRates : 2 * (2 * Real.sqrt 2 * changed.omega (index.val + 1)) ≤
      (1 / 16 : ℝ) * changed.omega (source.val + 1) := by
    have recurrence : changed.omega (source.val + 1) = changed.omega (index.val + 1) * changed.ratio := by
      rw [← adjacent]
      simp only [Scales.omega, pow_succ]
      ring
    rw [recurrence]
    have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
    have sqrtTwo : Real.sqrt 2 ≤ 2 := by norm_num [Real.sqrt_le_iff]
    have ratioActual : 128 ≤ changed.ratio := ratioLarge
    nlinarith only [mul_le_mul_of_nonneg_right ratioActual omegaPositive.le,
      mul_le_mul_of_nonneg_right sqrtTwo omegaPositive.le]
  refine ⟨⟨extentFour, magnitudeNonnegative⟩, finerEq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro other finer
    rw [finerEq other finer]
    exact ⟨le_rfl, path.stopPositive.le, (by linarith only [radiusLarge]), sourceLarge, directionNorm,
      firstInitial, secondInitial, projectionInitial, upperInitial⟩
  · intro other finer time inside
    have zero : time = 0 := le_antisymm inside.2 inside.1
    subst time
    rw [finerEq other finer]
    constructor
    · intro patch
      exact (referenceExtent patch).trans (mul_le_mul_of_nonneg_right
        (by linarith only [extentFour] : (2 : ℝ) ≤ extent) (changed.length_pos _).le)
    · intro patch
      exact (actualExtent patch).trans (mul_le_mul_of_nonneg_right
        (by linarith only [boundExtent] : modelBound ≤ extent) (changed.length_pos _).le)
  · intro other finer time inside
    have zero : time = 0 := le_antisymm inside.2 inside.1
    subst time
    rw [finerEq other finer]
    simpa only [sub_self, mul_zero, Real.exp_zero, mul_one] using sharp
  · intro other finer time inside patch
    have zero : time = 0 := le_antisymm inside.2 inside.1
    subst time
    rw [finerEq other finer]
    exact domains patch
  · intro other finer
    rw [finerEq other finer]
    exact sourceRates
  · have nearest : index.val + 2 = count := by omega
    simp [nearest, Scales.predictedTime]
  · intro other finer
    simp [finerEq other finer, terminal, Scales.predictedTime]

end EulerNonuniqueness.Paper
