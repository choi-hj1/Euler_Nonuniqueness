import EulerNonuniqueness.Section5.CascadeMatchedPassageContinuation
import EulerNonuniqueness.Section5.CascadeTerminalSectionContinuation
import EulerNonuniqueness.Section6.SourcePacketRhombusJointContinuation
import EulerNonuniqueness.Section5.CascadeRhombusStrictGap

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000

theorem Scales.eventually_actual_stage_mechanical_completion (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit) (sectionTime incomingTime : ℝ)
    (timeOrder : incomingTime < sectionTime)
    {factor threshold scaleRoot boundaryConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1 / 8) (thresholdSmall : threshold ≤ 1 / 2)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (referenceSeparated : ∀ time : ℝ, ∀ target source : Fin 4, source ≠ target →
      2 * factor ≤ ‖centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) target -
        centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) source‖)
    (distanceLarge : 512 ≤ separationRadius orbit sectionTime)
    (separationClose : ‖orbit.positive sectionTime + orbit.negative sectionTime -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ 1 / 128)
    (referenceOutgoing : (7 / 8 : ℝ) * separationRadius orbit sectionTime ≤
      (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
        (orbit.positive sectionTime - orbit.negative sectionTime)).re) :
    ∃ tolerance > (0 : ℝ), ∀ᶠ frequency : ℝ in atTop,
    ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared,
    (∀ index : Fin count, index.val + 1 < count →
      (∀ time ∈ Icc 0 path.stop, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) ∨
      ∃ start ∈ Icc 0 path.stop, ∃ rotation : ℂ, ‖rotation‖ = 1 ∧
        ‖cascadeNormalizedPointPositions {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion
          index start rotation 0 - centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ ≤ tolerance) →
    path.stop = 1 := by
  classical
  obtain ⟨tolerance, tolerancePositive, passage⟩ := scales.eventually_material_matched_passage_continuation
    amplitudePositive ratioBound alphaPositive orbit normalized sectionTime incomingTime sectionTime timeOrder
    factorPositive factorSmall rootPositive boundaryNonnegative (by norm_num : (0 : ℝ) < 1 / 64)
    (by norm_num : (1 / 64 : ℝ) ≤ 1 / 64) referenceSeparated distanceLarge
    (by convert separationClose using 1 <;> norm_num) referenceOutgoing
  refine ⟨tolerance, tolerancePositive, ?_⟩
  filter_upwards [passage,
    cascade_terminal_gap_continuation_of_section orbit sectionTime distanceLarge separationClose referenceOutgoing
      scales amplitudePositive ratioBound alphaPositive factorPositive factorSmall rootPositive boundaryNonnegative,
    scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative] with frequency passage terminal rhombus
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path stages
  by_contra incomplete
  have premature : path.stop < 1 := lt_of_le_of_ne path.stopBound incomplete
  obtain ⟨index, first, second, different, contact⟩ := path.premature_contact premature
  have lengthPositive := ({scales with frequency := frequency} : Scales).length_pos (index.val + 1)
  have endpoint : path.stop ∈ Icc 0 path.stop := ⟨path.stopPositive.le, le_rfl⟩
  by_cases last : index.val + 1 = count
  · have gap := terminal count phase dipoleAngle prepared path index last path.stop endpoint first second different
    have scaled := mul_le_mul_of_nonneg_right factorSmall lengthPositive.le
    nlinarith
  have nonterminal : index.val + 1 < count := by omega
  rcases stages index nonterminal with radial | ⟨start, startInside, rotation, rotationNorm, matched⟩
  · have invariants := rhombus prepared path thresholdSmall factorSmall index nonterminal path.stop
      path.stopPositive.le le_rfl radial path.stop endpoint
    have lower : ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 / 2 ≤
        diagonalDifference prepared.trajectory.movingFamily.patchMotion path.stop index := by
      have bound := (abs_le.mp invariants.1).1
      have squarePositive := sq_pos_of_pos lengthPositive
      have ratioLower : (3 / 4 : ℝ) ≤ diagonalDifference prepared.trajectory.movingFamily.patchMotion path.stop index /
          ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 := by linarith only [bound]
      rw [le_div_iff₀ squarePositive] at ratioLower
      nlinarith only [ratioLower, squarePositive]
    have neutral : ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion path.stop index‖ ≤
        ({scales with frequency := frequency} : Scales).length (index.val + 1) / 64 := by
      linarith only [invariants.2, lengthPositive]
    have gap := patchCentroid_pair_strict_eighth_of_rhombus_shape prepared.trajectory.movingFamily.patchMotion
      path.stop index lengthPositive lower (radial path.stop endpoint) neutral first second different
    have scaled := mul_le_mul_of_nonneg_right factorSmall lengthPositive.le
    nlinarith
  · have gap := passage count phase dipoleAngle prepared path index start startInside.1 startInside.2
      rotation rotationNorm matched path.stop ⟨startInside.2, le_rfl⟩ first second different
    linarith

end EulerNonuniqueness.Paper
