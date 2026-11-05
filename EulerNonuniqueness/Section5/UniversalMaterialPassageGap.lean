import EulerNonuniqueness.Section5.UniversalMaterialPassageShadowing
import EulerNonuniqueness.Section6.CenteredPassageGapImprovement

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_universal_material_paper_label_passage_strict_gap
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (incomingTime horizon : ℝ) (horizonPositive : 0 < horizon)
    {factor : ℝ} (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (referenceSeparated : ∀ time : ℝ, ∀ target source : Fin 4, source ≠ target →
      2 * factor ≤ ‖centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) target -
        centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) source‖) :
    ∃ tolerance > (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ sectionTime : ℝ, ∀ {threshold scaleRoot boundaryConstant : ℝ},
    0 < scaleRoot → 0 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop,
    ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, ∀ start window : ℝ,
    0 < window → window ≤ horizon → ∀ rotation : ℂ, ‖rotation‖ = 1 →
    (∀ time ∈ Icc 0 window, start + time / ({scales with frequency := frequency} : Scales).omega (index.val + 1) ∈ Icc 0 path.stop) →
    ‖cascadeNormalizedPointPositions {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion
      index start rotation 0 - centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ ≤ tolerance →
    ∀ time ∈ Icc 0 window, ∀ target source : Fin 4, source ≠ target →
      factor < ‖cascadeNormalizedPointPositions {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion
        index start rotation time target - cascadeNormalizedPointPositions {scales with frequency := frequency}
          prepared.trajectory.movingFamily.patchMotion index start rotation time source‖ := by
  obtain ⟨tolerance, tolerancePositive, shadowing⟩ :=
    exists_universal_material_paper_label_passage_shadowing orbit normalized incomingTime horizon horizonPositive
      (factor / 2) (by positivity) factorPositive factorSmall
  refine ⟨tolerance, tolerancePositive, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive sectionTime threshold scaleRoot boundaryConstant rootPositive boundaryNonnegative
  filter_upwards [shadowing scales amplitudePositive ratioBound alphaPositive sectionTime
    (threshold := threshold) rootPositive boundaryNonnegative] with frequency shadowing
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path index start window windowPositive windowBound
    rotation rotationNorm inside initial time member target source different
  have close := shadowing count phase dipoleAngle prepared path index start window windowPositive windowBound
    rotation rotationNorm inside initial time member
  have gap := configuration_pair_gap_of_close close
    (fun target source different => by linarith [referenceSeparated (time + incomingTime) target source different])
    target source different
  simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using gap

end EulerNonuniqueness.Paper

