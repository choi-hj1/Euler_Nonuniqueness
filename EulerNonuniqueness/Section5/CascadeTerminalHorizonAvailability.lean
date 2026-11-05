import EulerNonuniqueness.Section5.CascadePrehitInternalGap
import EulerNonuniqueness.Section5.CascadeTerminalSectionContinuation

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem eventually_actual_terminal_horizon_available
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    (radiusLarge : 512 ≤ separationRadius orbit sectionTime)
    (separationClose : ‖orbit.positive sectionTime + orbit.negative sectionTime -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ 1 / 128)
    (outgoing : (7 / 8 : ℝ) * separationRadius orbit sectionTime ≤
      (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
        (orbit.positive sectionTime - orbit.negative sectionTime)).re)
    (scales : Scales) (amplitudePositive : 0 < scales.amplitude)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {factor threshold scaleRoot boundaryConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1 / 8)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, threshold ≤ 1 / 2 →
    ∀ horizon : ℝ, horizon < 1 →
    (∀ index : Fin count, index.val + 1 < count →
      ∀ time ∈ Icc 0 path.stop, time ≤ horizon →
        |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    horizon ≤ path.stop := by
  filter_upwards [
    scales.eventually_material_prehit_internal_gap amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative,
    cascade_terminal_gap_continuation_of_section orbit sectionTime radiusLarge separationClose outgoing
      scales amplitudePositive ratioBound alphaPositive (threshold := threshold)
      factorPositive factorSmall rootPositive boundaryNonnegative]
    with frequency prehit terminal
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path
    thresholdSmall horizon horizonSmall radial
  by_contra unavailable
  have stopBefore : path.stop < horizon := lt_of_not_ge unavailable
  have premature : path.stop < 1 := stopBefore.trans horizonSmall
  obtain ⟨index, first, second, different, contact⟩ := path.premature_contact premature
  by_cases last : index.val + 1 = count
  · have gap := terminal count phase dipoleAngle prepared path index last path.stop
      ⟨path.stopPositive.le, le_rfl⟩ first second different
    rw [contact] at gap
    have lengthPositive := ({scales with frequency := frequency} : Scales).length_pos (index.val + 1)
    nlinarith only [gap, factorSmall, lengthPositive]
  · have nonterminal : index.val + 1 < count := by omega
    have radialPrefix : ∀ time ∈ Icc 0 path.stop,
        |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2 := by
      intro time inside
      exact radial index nonterminal time inside (inside.2.trans stopBefore.le)
    have gap := (prehit prepared path thresholdSmall factorSmall index nonterminal path.stop
      path.stopPositive.le le_rfl radialPrefix path.stop ⟨path.stopPositive.le, le_rfl⟩).1
      first second different
    rw [contact] at gap
    exact (lt_irrefl _ gap)

end EulerNonuniqueness.Paper
