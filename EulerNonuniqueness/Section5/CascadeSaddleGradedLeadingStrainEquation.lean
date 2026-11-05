import EulerNonuniqueness.Section5.CascadeSaddleLeadingStrainEquation
import EulerNonuniqueness.Section5.CascadeSaddleGradedIndexDecayDynamics

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_saddle_graded_leading_strain_equation :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ chartConstant ≥ (1 : ℝ), ∃ pointConstant ≥ (1 : ℝ), ∃ forcingConstant ≥ (1 : ℝ),
      ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
      ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ),
      ∀ {scaleRoot boundaryConstant factor threshold coarseConstant tolerance : ℝ},
      1 ≤ scaleRoot → 1 ≤ boundaryConstant → 0 < factor → factor ≤ 1 / 8 →
      threshold ≤ thresholdMax → 0 ≤ coarseConstant → 0 < tolerance →
      ∀ᶠ frequency : ℝ in atTop,
      ∀ {phase dipoleAngle : ℕ → ℝ} {shapeRadius monitor : ℝ} {count : ℕ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold coarseConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared,
      ∀ index : Fin count, index.val + 1 < count → ∀ time ∈ Ioo 0 path.stop,
      (∀ current ∈ Icc 0 time,
        |unstableShape prepared.trajectory.movingFamily.patchMotion current index| +
          |stableShape prepared.trajectory.movingFamily.patchMotion current index| ≤ radius) →
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      let firstChart := referenceStraightenedShape first graph coordinate index time
      let secondChart := referenceStraightenedShape second graph coordinate index time
      let difference := |firstChart.1 - secondChart.1| + |firstChart.2 - secondChart.2|
      let length := changed.length (index.val + 1)
      let sourceRadius := factor / 39321600 * changed.location (index.val + 1)
      let positions := ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length
      let dilationDifference := |diagonalDifference first time index - diagonalDifference second time index| / length ^ 2
      let referenceSize := chartConstant * coarseConstant *
        ((changed.strain + changed.strain ^ 2) / changed.omega (index.val + 1) + (changed.omega (index.val + 1))⁻¹ ^ 5)
      let leading := quadrupoleRelativeLeadingStrain changed first second time index
      HasDerivAt (fun current => referenceStraightenedShape first graph coordinate index current -
          referenceStraightenedShape second graph coordinate index current)
        ((2 * Real.sqrt 2 * changed.omega (index.val + 1) * (firstChart.1 - secondChart.1),
            -(2 * Real.sqrt 2 * changed.omega (index.val + 1)) * (firstChart.2 - secondChart.2)) +
          leading + relativeStraightenedSaddleStrainRemainder changed (cascadePairedMotion prepared) graph coordinate index time) time ∧
      ‖relativeStraightenedSaddleStrainRemainder changed (cascadePairedMotion prepared) graph coordinate index time‖ ≤
        pointConstant * |changed.omega (index.val + 1)| *
          ((referenceSize + dilationDifference + |firstChart.2 - secondChart.2|) * difference + referenceSize * dilationDifference) +
        (tolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ + positions +
            |unstableShape first time index - unstableShape second time index|) +
          30 * forcingConstant * (‖quadrupoleDilationPatchError changed first index time -
            quadrupoleDilationPatchError changed second index time‖ / length) +
          30 * forcingConstant * ((length / sourceRadius) * (6 * (96 / Real.pi * (2304 * changed.strain)) * positions +
            9 * (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time sourceRadius (power + 1) -
              quadrupoleExteriorCoefficient changed second index time sourceRadius (power + 1)‖))) +
          forcingConstant * |unstableShape second time index| * ‖leading‖) := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, pointConstant, pointOne, thresholdMax, thresholdPositive,
    thresholdEighth, pointRadius, pointPositive, pointQuarter, compatible, dynamics⟩ :=
    exists_uniform_cascade_saddle_graded_index_decay_dynamics
  obtain ⟨forcingRadius, forcingPositive, _, forcingConstant, forcingOne, forcing⟩ :=
    exists_uniform_cascade_straightened_forcing_small_input graphAnalytic.contDiffAt coordinateSmooth
      graphDerivative coordinateDerivative
  let radius := min pointRadius forcingRadius
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, pointConstant, pointOne, forcingConstant, forcingOne,
    thresholdMax, thresholdPositive, thresholdEighth, radius, lt_min pointPositive forcingPositive,
    (min_le_left _ _).trans pointQuarter, compatible, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant factor threshold
    coarseConstant tolerance rootOne boundaryOne factorPositive factorSmall thresholdSmall coarseNonnegative tolerancePositive
  have rootPositive : 0 < scaleRoot := zero_lt_one.trans_le rootOne
  have boundaryNonnegative : 0 ≤ boundaryConstant := zero_le_one.trans boundaryOne
  filter_upwards [dynamics scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
      factorPositive factorSmall thresholdSmall coarseNonnegative,
    forcing scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      (thresholdSmall.trans thresholdEighth) coarseNonnegative factorPositive factorSmall tolerancePositive]
    with frequency actualDynamics actualForcing
  intro phase dipoleAngle shapeRadius monitor count prepared path index nonterminal time inside small
  dsimp only
  have actual := actualDynamics prepared path index nonterminal time inside
    (fun current member => (small current member).trans (min_le_left _ _))
  have radial : ∀ current ∈ Icc 0 time,
      |radialShape prepared.trajectory.movingFamily.patchMotion current index| ≤ 1 / 2 := by
    intro current member
    rw [radialShape_eq_unstable_add_stable]
    exact (abs_add _ _).trans ((small current member).trans
      ((min_le_left _ _).trans (pointQuarter.trans (by norm_num))))
  have forceBound := actualForcing count phase dipoleAngle prepared path index nonterminal time inside.1.le inside.2.le
    radial time ⟨inside.1.le, le_rfl⟩ ((small time ⟨inside.1.le, le_rfl⟩).trans (min_le_right _ _))
  refine ⟨?_, ?_⟩
  · have derivative := actual.1
    rw [relativeStraightenedSaddleVelocity_eq_leading_strain] at derivative
    exact derivative
  · have triangle := norm_add_le
      (relativeStraightenedSaddlePointRemainder {scales with frequency := frequency} (cascadePairedMotion prepared) graph coordinate index time)
      (referenceStraightenedForcing {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion graph coordinate index time -
        referenceStraightenedForcing {scales with frequency := frequency} prepared.reference graph coordinate index time -
          quadrupoleRelativeLeadingStrain {scales with frequency := frequency}
            prepared.trajectory.movingFamily.patchMotion prepared.reference time index)
    exact triangle.trans (add_le_add actual.2 forceBound)

end EulerNonuniqueness.Paper
