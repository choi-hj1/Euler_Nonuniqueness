import EulerNonuniqueness.Section5.CascadeFollowerDrivenEnvelopeVolterra
import EulerNonuniqueness.Section5.CascadeSelectedForeignForcingContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000

theorem Scales.eventually_cascade_follower_finer_forcing_continuous (scales : Scales)
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
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ drive : Fin count,
    (∀ time : ℝ, 0 ≤ prepared.followerStrictlyFinerForcing drive time) ∧
    ContinuousOn (prepared.followerStrictlyFinerForcing drive) (Icc 0 path.stop) ∧
    ∀ start finish : ℝ, 0 ≤ start → start ≤ finish → finish ≤ path.stop → ∀ weight : ℝ,
      IntervalIntegrable (fun time => Real.exp (-weight * (time - start)) *
        prepared.followerStrictlyFinerForcing drive time) volume start finish := by
  filter_upwards [scales.eventually_cascade_selected_foreign_forcing_continuous amplitudePositive ratioBound alphaPositive
    orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall]
    with frequency selectedContinuous
  intro count phase dipoleAngle cap shapeRadius monitor prepared path drive
  let changed : Scales := {scales with frequency := frequency}
  let selected := fun receiver : Fin count => Finset.univ.filter
    (fun source : Fin count => drive.val < source.val ∧ source ≠ receiver)
  have subset (receiver : Fin count) : selected receiver ⊆ Finset.univ.erase receiver := by
    intro source member
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp member).2.2, Finset.mem_univ _⟩
  have regular (receiver : Fin count) :
      ContinuousOn (prepared.selectedForeignForcing (selected receiver) receiver) (Icc 0 path.stop) :=
    (selectedContinuous count phase dipoleAngle prepared path receiver (selected receiver) (subset receiver)).2.1
  have forcingContinuous : ContinuousOn (prepared.followerStrictlyFinerForcing drive) (Icc 0 path.stop) := by
    apply ContinuousOn.norm
    apply continuousOn_pi.mpr
    intro receiver
    by_cases below : receiver.val < drive.val
    · simpa only [below, ite_true] using (continuousOn_const.mul (regular receiver) :
        ContinuousOn (fun time => changed.location (receiver.val + 1) ^ 4 *
          prepared.selectedForeignForcing (selected receiver) receiver time) (Icc 0 path.stop))
    · simpa only [below, ite_false] using
        (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 path.stop))
  refine ⟨fun _ => norm_nonneg _, forcingContinuous, ?_⟩
  intro start finish startNonnegative ordered finishBound weight
  have exponentialContinuous : Continuous (fun time : ℝ => Real.exp (-weight * (time - start))) := by fun_prop
  exact (exponentialContinuous.continuousOn.mul
    (forcingContinuous.mono (Icc_subset_Icc startNonnegative finishBound))).intervalIntegrable_of_Icc ordered

end EulerNonuniqueness.Paper
