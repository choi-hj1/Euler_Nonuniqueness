import EulerNonuniqueness.Section5.CascadeStraightenedForcingInput
import EulerNonuniqueness.Section5.CascadePrehitPointForcingSmall
import EulerNonuniqueness.Section5.CascadeReferenceSharpDefect

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_straightened_forcing_small_input
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ chartRadius > (0 : ℝ), chartRadius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ),
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
      |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ chartRadius →
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
        tolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ + positions +
          |unstableShape first time index - unstableShape second time index|) +
        30 * constant * (‖quadrupoleDilationPatchError changed first index time - quadrupoleDilationPatchError changed second index time‖ / length) +
        30 * constant * ((length / radius) * (6 * (96 / Real.pi * (2304 * changed.strain)) * positions +
          9 * (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius (power + 1) -
            quadrupoleExteriorCoefficient changed second index time radius (power + 1)‖))) +
        constant * |unstableShape second time index| * ‖leading‖ := by
  obtain ⟨baseRadius, basePositive, constant, constantOne, transformed⟩ :=
    exists_uniform_cascade_straightened_forcing_input graphSmooth coordinateSmooth graphDerivative coordinateDerivative
  let chartRadius := min baseRadius (1 / 4)
  have chartPositive : 0 < chartRadius := lt_min basePositive (by norm_num)
  have chartQuarter : chartRadius ≤ 1 / 4 := min_le_right _ _
  have chartBase : chartRadius ≤ baseRadius := min_le_left _ _
  have constantPositive : 0 < constant := zero_lt_one.trans_le constantOne
  refine ⟨chartRadius, chartPositive, chartQuarter, constant, constantOne, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold
    referenceConstant factor tolerance rootOne boundaryOne thresholdSmall referenceNonnegative factorPositive
    factorSmall tolerancePositive
  have smallPositive : 0 < tolerance / constant := div_pos tolerancePositive constantPositive
  filter_upwards [transformed scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      thresholdSmall referenceNonnegative factorPositive factorSmall smallPositive,
    scales.eventually_cascade_prehit_point_forcing_small amplitudePositive ratioBound alphaPositive orbit sectionTime
      rootOne boundaryOne thresholdSmall referenceNonnegative factorPositive factorSmall smallPositive,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative basePositive]
    with frequency actual pointSmall referenceSmall
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radial
    time inside currentSmall
  have firstSmall : |unstableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ baseRadius :=
    (le_add_of_nonneg_right (abs_nonneg _)).trans (currentSmall.trans chartBase)
  have secondSmall : |unstableShape prepared.reference time index| ≤ baseRadius := by
    have sharp := referenceSmall prepared time
      (show time ∈ Icc (0 : ℝ) 1 from ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩) index
    linarith [abs_nonneg (diagonalDifference prepared.reference time index /
      ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 - 1),
      abs_nonneg (stableShape prepared.reference time index)]
  have bound := actual count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radial
    time inside firstSmall secondSmall
  have small := pointSmall count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radial
    time inside (currentSmall.trans chartQuarter)
  dsimp only at bound ⊢
  have error := mul_le_mul_of_nonneg_left small
    (mul_nonneg constantPositive.le (abs_nonneg
      (unstableShape prepared.trajectory.movingFamily.patchMotion time index - unstableShape prepared.reference time index)))
  have enlarged := bound.trans (add_le_add_left error _)
  have scalarIdentity (moment positions shape patch tail leading : ℝ) :
      constant * (tolerance / constant * (moment + positions) + 30 * patch + 30 * tail) +
          leading + constant * shape * (tolerance / constant) =
        tolerance * (moment + positions + shape) + 30 * constant * patch +
          30 * constant * tail + leading := by
    field_simp
    <;> ring
  calc
    _ ≤ _ := enlarged
    _ = _ := scalarIdentity _ _ _ _ _ _

end EulerNonuniqueness.Paper
