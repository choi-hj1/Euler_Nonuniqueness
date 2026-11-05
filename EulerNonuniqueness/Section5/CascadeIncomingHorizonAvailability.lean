import EulerNonuniqueness.Section5.CascadePrehitInternalGap
import EulerNonuniqueness.Section5.CascadeOutgoingInternalGap

noncomputable section
open Set Filter
open scoped Topology
namespace EulerNonuniqueness.Paper
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem Scales.eventually_actual_incoming_horizon_available (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {factor threshold scaleRoot boundaryConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1 / 8)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, threshold ≤ 1 / 2 →
    ∀ receiver : Fin count, receiver.val + 1 < count →
    ∀ entry initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    (∀ source : Fin count, receiver.val < source.val →
      let length := changed.length (source.val + 1)
      0 ≤ entry source ∧ entry source ≤ path.stop ∧ 512 ≤ initialDistance source ∧
      initialDistance source ≤ changed.omega (source.val + 1) / 16 ∧ ‖direction source‖ = 1 ∧
      ‖firstDipoleSeparation motion (entry source) source - (length : ℂ) * direction source‖ ≤ length / 64 ∧
      ‖secondDipoleSeparation motion (entry source) source - (length : ℂ) * (-direction source)‖ ≤ length / 64 ∧
      (3 / 4 : ℝ) * length * initialDistance source ≤
        (Complex.I * star (direction source) * (firstDipoleCenter motion (entry source) source -
          secondDipoleCenter motion (entry source) source)).re ∧
      ‖firstDipoleCenter motion (entry source) source - secondDipoleCenter motion (entry source) source‖ ≤
        (5 / 4 : ℝ) * length * initialDistance source) →
    ∀ horizon : ℝ, horizon < 1 →
    (∀ current : Fin count, current.val ≤ receiver.val →
      ∀ time ∈ Icc 0 path.stop, time ≤ horizon → |radialShape motion time current| ≤ 1 / 2) →
    horizon ≤ path.stop := by
  filter_upwards [scales.eventually_material_prehit_internal_gap amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative,
    scales.eventually_material_outgoing_internal_gap amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive (factorSmall.trans (by norm_num)) rootPositive boundaryNonnegative]
    with frequency prehit outgoing
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path thresholdSmall receiver nonterminal
    entry initialDistance direction
  dsimp only
  intro entries horizon horizonSmall radial
  by_contra unavailable
  have stopBefore : path.stop < horizon := lt_of_not_ge unavailable
  have premature : path.stop < 1 := stopBefore.trans horizonSmall
  obtain ⟨index, first, second, different, contact⟩ := path.premature_contact premature
  by_cases lower : index.val ≤ receiver.val
  · have indexNonterminal : index.val + 1 < count := by omega
    have radialPrefix : ∀ time ∈ Icc 0 path.stop,
        |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2 := by
      intro time inside
      exact radial index lower time inside (inside.2.trans stopBefore.le)
    have gap := (prehit prepared path thresholdSmall factorSmall index indexNonterminal path.stop
      path.stopPositive.le le_rfl radialPrefix path.stop ⟨path.stopPositive.le, le_rfl⟩).1 first second different
    rw [contact] at gap
    exact (lt_irrefl _ gap)
  · have finer : receiver.val < index.val := lt_of_not_ge lower
    obtain ⟨startNonnegative, startBound, distanceLarge, distanceSmall, directionNorm,
      firstInitial, secondInitial, initialProjection, initialUpper⟩ := entries index finer
    have durationNonnegative : 0 ≤ path.stop - entry index := sub_nonneg.mpr startBound
    have durationBound : path.stop - entry index ≤ 1 := by linarith only [path.stopBound, startNonnegative]
    have endIdentity : entry index + (path.stop - entry index) = path.stop := by ring
    have gap := outgoing count phase dipoleAngle prepared path index (entry index) (path.stop - entry index)
      (initialDistance index) startNonnegative durationNonnegative durationBound (by rw [endIdentity]) distanceLarge distanceSmall
      (direction index) directionNorm firstInitial secondInitial initialProjection initialUpper
      (path.stop - entry index) ⟨durationNonnegative, le_rfl⟩ first second different
    rw [endIdentity, contact] at gap
    have lengthPositive := ({scales with frequency := frequency} : Scales).length_pos (index.val + 1)
    nlinarith only [gap, factorSmall, lengthPositive]

end EulerNonuniqueness.Paper
