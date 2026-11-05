import EulerNonuniqueness.Section5.CascadeSourcePreparedPair
import EulerNonuniqueness.Section5.CascadeForeignCoefficientSeriesContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

namespace CascadeSourcePreparedPair

variable {requestedCap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
  {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}

def physicalForeignSourceForcing
    (prepared : CascadeSourcePreparedPair requestedCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (index : Fin count) (time : ℝ) : ℝ :=
  ∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid prepared.trajectory.movingFamily.patchMotion current index patch)
        (scales.radius (index.val + 1)) (power + 1) time -
      prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current index patch)
        (scales.radius (index.val + 1)) (power + 1) time‖

theorem physicalForeignSourceForcing_nonneg
    (prepared : CascadeSourcePreparedPair requestedCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (index : Fin count) (time : ℝ) : 0 ≤ prepared.physicalForeignSourceForcing index time := by
  apply Finset.sum_nonneg
  intro patch member
  exact tsum_nonneg (fun power => mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 96) _) (norm_nonneg _))

end CascadeSourcePreparedPair

theorem Scales.eventually_cascade_physical_foreign_forcing_continuous (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {requestedCap shapeRadius monitor : ℝ},
      ∀ prepared : CascadeSourcePreparedPair requestedCap {scales with frequency := frequency} orbit sectionTime
        phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ index : Fin count,
      (∀ patch : Fin 4, ∀ time ∈ Icc 0 path.stop,
        Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
          ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
              (fun current => patchCentroid prepared.trajectory.movingFamily.patchMotion current index patch)
              (({scales with frequency := frequency} : Scales).radius (index.val + 1)) (power + 1) time -
            prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
              (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current index patch)
              (({scales with frequency := frequency} : Scales).radius (index.val + 1)) (power + 1) time‖)) ∧
      ContinuousOn (prepared.physicalForeignSourceForcing index) (Icc 0 path.stop) ∧
      (∀ time : ℝ, 0 ≤ prepared.physicalForeignSourceForcing index time) ∧
      IntervalIntegrable (prepared.physicalForeignSourceForcing index) volume 0 path.stop := by
  filter_upwards [scales.eventually_cascade_foreign_coefficient_series_continuous
      amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative
      rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio)
      (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive
      (by norm_num : (0 : ℝ) < 1 / (100000 * 96)),
    eventually_gt_atTop (0 : ℝ)]
    with frequency series radii lengths frequencyPositive
  intro count phase dipoleAngle requestedCap shapeRadius monitor prepared path index
  let changed : Scales := {scales with frequency := frequency}
  have radiusNonnegative : 0 ≤ changed.radius (index.val + 1) :=
    (changed.radius_pos amplitudePositive frequencyPositive
      (by change 0 < scales.ratio; linarith only [ratioBound]) _).le
  have radiusSmall : changed.radius (index.val + 1) ≤ scales.location (index.val + 1) / (100000 * 96) := by
    have first := (radii (index.val + 1)).le
    have second := (lengths (index.val + 1)).le
    change changed.radius (index.val + 1) ≤ 1 * changed.length (index.val + 1) at first
    change changed.length (index.val + 1) ≤ (1 / (100000 * 96) : ℝ) * scales.location (index.val + 1) at second
    linarith only [first, second]
  have actual := (series count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index
    (changed.radius (index.val + 1)) radiusNonnegative radiusSmall).1
  have continuous : ContinuousOn (prepared.physicalForeignSourceForcing index) (Icc 0 path.stop) := by
    apply continuousOn_finset_sum
    intro patch member
    exact (actual patch).2
  exact ⟨fun patch => (actual patch).1, continuous,
    prepared.physicalForeignSourceForcing_nonneg index,
    continuous.intervalIntegrable_of_Icc path.stopPositive.le⟩

end EulerNonuniqueness.Paper

