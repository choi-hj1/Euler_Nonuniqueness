import EulerNonuniqueness.Section5.CascadePrehitRelativeShapeForcingInput
import EulerNonuniqueness.Section6.NormalFormForcingLocalRelative

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_straightened_forcing_input
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ chartRadius > (0 : ℝ), ∃ constant ≥ (1 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ),
    ∀ {scaleRoot boundaryConstant threshold referenceConstant factor tolerance : ℝ},
    1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    0 < factor → factor ≤ 1 / 8 → 0 < tolerance →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, index.val + 1 < count →
      ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      ∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ chartRadius →
      |unstableShape prepared.reference time index| ≤ chartRadius →
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      let length := changed.length (index.val + 1)
      let radius := factor / 39321600 * changed.location (index.val + 1)
      let positions := ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length
      let leading := quadrupoleRelativeLeadingStrain changed first second time index
      ‖referenceStraightenedForcing changed first graph coordinate index time -
          referenceStraightenedForcing changed second graph coordinate index time - leading‖ ≤
        constant * (tolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ + positions) +
          30 * (‖quadrupoleDilationPatchError changed first index time - quadrupoleDilationPatchError changed second index time‖ / length) +
          30 * ((length / radius) * (6 * (96 / Real.pi * (2304 * changed.strain)) * positions +
            9 * (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius (power + 1) -
              quadrupoleExteriorCoefficient changed second index time radius (power + 1)‖)))) +
        constant * |unstableShape second time index| * ‖leading‖ +
        constant * |unstableShape first time index - unstableShape second time index| *
          ‖referencePointShapeForcing changed first time index‖ := by
  obtain ⟨chartRadius, chartPositive, constant, constantOne, normalForm⟩ :=
    sameGraph_referenceStraightenedForcing_exists_local_relative_bound graphSmooth coordinateSmooth
      graphDerivative coordinateDerivative
  refine ⟨chartRadius, chartPositive, constant, constantOne, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold
    referenceConstant factor tolerance rootOne boundaryOne thresholdSmall referenceNonnegative factorPositive
    factorSmall tolerancePositive
  filter_upwards [scales.eventually_cascade_prehit_relative_shape_forcing_input amplitudePositive ratioBound alphaPositive
    orbit sectionTime rootOne boundaryOne thresholdSmall referenceNonnegative factorPositive factorSmall tolerancePositive]
    with frequency actualInput
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radial
    time inside firstSmall secondSmall
  dsimp only
  have raw := actualInput count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radial time inside
  have transformed := normalForm {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion
    prepared.reference index time firstSmall secondSmall
    (quadrupoleRelativeLeadingStrain {scales with frequency := frequency}
      prepared.trajectory.movingFamily.patchMotion prepared.reference time index)
  dsimp only at raw
  exact transformed.trans (add_le_add_right
    (add_le_add_right (mul_le_mul_of_nonneg_left raw (by linarith)) _) _)

end EulerNonuniqueness.Paper
