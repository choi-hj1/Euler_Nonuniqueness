import EulerNonuniqueness.Section5.CascadeForeignForcingPartition
import EulerNonuniqueness.Section5.CascadeIndividualSourceSeriesContinuity
import EulerNonuniqueness.Section5.CascadeIndividualSourceVelocityContinuity
import EulerNonuniqueness.Section5.CascadeIndividualSourceInputContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

theorem Scales.eventually_cascade_selected_foreign_forcing_continuous (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {cap shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair cap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ receiver : Fin count, ∀ selected : Finset (Fin count), selected ⊆ Finset.univ.erase receiver →
    (∀ time : ℝ, 0 ≤ prepared.selectedForeignForcing selected receiver time) ∧
    ContinuousOn (prepared.selectedForeignForcing selected receiver) (Icc 0 path.stop) ∧
    ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      IntervalIntegrable (prepared.selectedForeignForcing selected receiver) volume 0 finish := by
  filter_upwards [scales.eventually_cascade_individual_source_series_continuous amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_individual_source_velocity_continuous amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_individual_source_input_continuous amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio)
      (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / (100000 * 96))]
    with frequency series velocities inputs radii lengths
  intro count phase dipoleAngle cap shapeRadius monitor prepared path receiver selected subset
  let changed : Scales := {scales with frequency := frequency}
  let macroRadius := factor / 39321600 * changed.location (receiver.val + 1)
  let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
  have different (source : Fin count) (member : source ∈ selected) : receiver ≠ source :=
    (Finset.mem_erase.mp (subset member)).1.symm
  have locationPositive := changed.location_pos (receiver.val + 1)
  have lengthSmall : changed.length (receiver.val + 1) ≤ changed.location (receiver.val + 1) / (100000 * 96) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using (lengths (receiver.val + 1)).le
  have lengthBelow : changed.length (receiver.val + 1) ≤ changed.location (receiver.val + 1) :=
    lengthSmall.trans (div_le_self locationPositive.le (by norm_num))
  have physicalNonnegative : 0 ≤ changed.radius (receiver.val + 1) := Real.sqrt_nonneg _
  have physicalSmall : changed.radius (receiver.val + 1) ≤ scales.location (receiver.val + 1) / (100000 * 96) :=
    (show changed.radius (receiver.val + 1) ≤ changed.length (receiver.val + 1) by
      simpa only [one_mul] using (radii (receiver.val + 1)).le).trans lengthSmall
  have macroNonnegative : 0 ≤ macroRadius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) locationPositive.le
  have macroSmall : macroRadius ≤ scales.location (receiver.val + 1) / (100000 * 96) := by
    have scalar : factor / 39321600 ≤ 1 / (100000 * 96) := by linarith only [factorSmall]
    simpa only [macroRadius, div_eq_mul_inv, one_mul, mul_comm] using
      mul_le_mul_of_nonneg_right scalar locationPositive.le
  have ownNonnegative : 0 ≤ ownRadius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) (changed.length_pos _).le
  have ownSmall : ownRadius ≤ scales.location (receiver.val + 1) / (100000 * 96) :=
    (mul_le_mul_of_nonneg_left lengthBelow (div_nonneg factorPositive.le (by norm_num))).trans macroSmall
  have leading : ContinuousOn (fun time =>
      ‖∑ source ∈ selected, relativeBlockSourceShapeInput changed prepared.trajectory.movingFamily.patchMotion
        prepared.reference receiver source time‖) (Icc 0 path.stop) := by
    apply ContinuousOn.norm
    apply continuousOn_finset_sum
    intro source member
    exact inputs count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver source (different source member)
  have block : ContinuousOn (fun time => ∑ source ∈ selected,
      ∑' power : ℕ, prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) (Icc 0 path.stop) := by
    apply continuousOn_finset_sum
    intro source member
    exact (series count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver source (different source member)
      macroRadius macroNonnegative macroSmall).2.1
  have patch (radius : ℝ) (nonnegative : 0 ≤ radius)
      (small : radius ≤ scales.location (receiver.val + 1) / (100000 * 96)) :
      ContinuousOn (fun time => ∑ patch : Fin 4, ∑ source ∈ selected,
        ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source power) (Icc 0 path.stop) := by
    apply continuousOn_finset_sum
    intro patch patchMember
    apply continuousOn_finset_sum
    intro source member
    exact ((series count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver source (different source member)
      radius nonnegative small).2.2 patch).2
  have velocity : ContinuousOn (fun time => (∑ patch : Fin 4, ∑ source ∈ selected,
      ‖biotSavart (quadrupoleDensity changed prepared.trajectory.movingFamily.patchMotion time source)
          (patchCentroid prepared.trajectory.movingFamily.patchMotion time receiver patch) -
        biotSavart (quadrupoleDensity changed prepared.reference time source)
          (patchCentroid prepared.reference time receiver patch)‖) / (4 * changed.location (receiver.val + 1)))
      (Icc 0 path.stop) := by
    apply ContinuousOn.div_const
    apply continuousOn_finset_sum
    intro patch patchMember
    apply continuousOn_finset_sum
    intro source member
    have actual := (velocities count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path
      (receiver, patch) source (different source member)).norm
    rw [prepared.referenceIdentity]
    exact actual
  have regular : ContinuousOn (prepared.selectedForeignForcing selected receiver) (Icc 0 path.stop) :=
    ((((leading.add block).add (continuousOn_const.mul (patch macroRadius macroNonnegative macroSmall))).add
      (continuousOn_const.mul (patch ownRadius ownNonnegative ownSmall))).add
      (patch _ physicalNonnegative physicalSmall)).add velocity
  refine ⟨?_, regular, ?_⟩
  · intro time
    dsimp only [CascadeSourcePreparedPair.selectedForeignForcing,
      CascadeSourcePreparedPair.coarserBlockCoefficientTerm, CascadeSourcePreparedPair.coarserPatchCoefficientTerm]
    positivity
  · intro finish finishNonnegative finishBound
    exact (regular.mono (Icc_subset_Icc le_rfl finishBound)).intervalIntegrable_of_Icc finishNonnegative

end EulerNonuniqueness.Paper
