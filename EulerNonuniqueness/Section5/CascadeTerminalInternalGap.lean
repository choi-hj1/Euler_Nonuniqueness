import EulerNonuniqueness.Section5.CascadeOutgoingInternalGap
import EulerNonuniqueness.Section5.CascadeTerminalOutgoingData
import EulerNonuniqueness.Section5.CascadeStoppedMaterialGeometry

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_cascade_terminal_gap_continuation (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) :
    ∃ sectionTime > (0 : ℝ), ∀ scales : Scales,
    0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {factor threshold scaleRoot boundaryConstant : ℝ}, 0 < factor → factor ≤ 1 / 8 →
    0 < scaleRoot → 0 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, index.val + 1 = count →
    ∀ time ∈ Icc 0 path.stop, ∀ first second : Fin 4, first ≠ second →
      ({scales with frequency := frequency} : Scales).length (index.val + 1) / 2 ≤
        ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time index first -
          patchCentroid prepared.trajectory.movingFamily.patchMotion time index second‖ := by
  obtain ⟨sectionTime, sectionPositive, radiusLarge, initialData⟩ :=
    exists_cascade_terminal_outgoing_initial_data orbit normalized
  refine ⟨sectionTime, sectionPositive, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive factor threshold scaleRoot boundaryConstant
    factorPositive factorSmall rootPositive boundaryNonnegative
  filter_upwards [scales.eventually_material_outgoing_internal_gap amplitudePositive ratioBound alphaPositive
      orbit sectionTime factorPositive (by linarith : factor ≤ 1) rootPositive boundaryNonnegative,
    eventually_ge_atTop (max 64 (16 * separationRadius orbit sectionTime))]
    with frequency outgoing frequencyLarge
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path index last
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := by
    change 0 < frequency
    have bound := (le_max_left (64 : ℝ) _).trans frequencyLarge
    linarith
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have initial := initialData path.evolution path.stopPositive.le amplitudePositive frequencyPositive
    ratioPositive prepared.commonInitial index last
  dsimp only at initial
  let direction := Complex.exp (Complex.I * (dipoleAngle count - orbit.limitingDipoleAngle : ℝ)) *
    Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))
  have directionNorm : ‖direction‖ = 1 := by simp [direction, norm_mul, Complex.norm_exp, Complex.mul_re]
  have initialSmall : separationRadius orbit sectionTime ≤ changed.omega (index.val + 1) / 16 := by
    have bound := (le_max_right (64 : ℝ) _).trans frequencyLarge
    have omegaBound := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) (index.val + 1)
    change frequency ≤ changed.omega (index.val + 1) at omegaBound
    linarith
  have result := outgoing count phase dipoleAngle prepared path index 0 path.stop
    (separationRadius orbit sectionTime) (by norm_num) path.stopPositive.le path.stopBound
    (by simp) radiusLarge initialSmall direction directionNorm
  dsimp only at result
  have firstInitial : ‖firstDipoleSeparation prepared.trajectory.movingFamily.patchMotion 0 index -
      (changed.length (index.val + 1) : ℂ) * direction‖ ≤ changed.length (index.val + 1) / 64 := by
    simpa [firstDipoleSeparation, relabelNegativePoints, negativeLabelSwap, Equiv.swap_apply_def,
      direction, changed, last] using initial.1
  have secondInitial : ‖secondDipoleSeparation prepared.trajectory.movingFamily.patchMotion 0 index -
      (changed.length (index.val + 1) : ℂ) * (-direction)‖ ≤ changed.length (index.val + 1) / 64 := by
    simpa [secondDipoleSeparation, relabelNegativePoints, negativeLabelSwap, Equiv.swap_apply_def,
      direction, changed, last] using initial.2.1
  have projectionInitial : (3 / 4 : ℝ) * changed.length (index.val + 1) * separationRadius orbit sectionTime ≤
      (Complex.I * star direction * (firstDipoleCenter prepared.trajectory.movingFamily.patchMotion 0 index -
        secondDipoleCenter prepared.trajectory.movingFamily.patchMotion 0 index)).re := by
    simpa [firstDipoleCenter, secondDipoleCenter, relabelNegativePoints, negativeLabelSwap,
      Equiv.swap_apply_def, direction, changed, last] using initial.2.2.1
  have upperInitial : ‖firstDipoleCenter prepared.trajectory.movingFamily.patchMotion 0 index -
      secondDipoleCenter prepared.trajectory.movingFamily.patchMotion 0 index‖ ≤
      (5 / 4 : ℝ) * changed.length (index.val + 1) * separationRadius orbit sectionTime := by
    simpa [firstDipoleCenter, secondDipoleCenter, relabelNegativePoints, negativeLabelSwap,
      Equiv.swap_apply_def, changed, last] using initial.2.2.2
  simpa only [zero_add] using result firstInitial secondInitial projectionInitial upperInitial

end EulerNonuniqueness.Paper
