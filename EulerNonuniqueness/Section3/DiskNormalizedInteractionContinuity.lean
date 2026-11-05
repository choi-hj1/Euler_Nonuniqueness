import EulerNonuniqueness.Section3.DiskNormalizedQuadraticObservable
import EulerNonuniqueness.Section3.DiskPhysicalScaledGroup
import EulerNonuniqueness.General.LocalRegularityNeighborhood
import EulerNonuniqueness.General.OperatorEvaluationContinuity

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] physicalGeneratorC1Space physicalGeneratorC1ContinuousAdd
  physicalGeneratorC1UniformAdd physicalGeneratorC1BoundedSMul
  physicalGeneratorOperatorGroup physicalGeneratorOperatorSpace
  physicalScaledOperatorModule physicalScaledOperatorBoundedSMul

local instance normalizedInteractionContinuityC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskNormalizedInteraction_exists_uniform_continuity :
    ∃ radius > 0, ∀ {curve : ℝ → PeriodicC1HolderHalf} {time frequency : ℝ},
      ‖curve time - standardCircleBanach‖ ≤ radius → ContinuousAt curve time →
      ContinuousAt (fun current => diskPhysicalScaledGroup frequency (-current)
        (diskNormalizedQuadraticObservable (curve current))) time := by
  have nearby : ∀ᶠ data in 𝓝 standardCircleBanach,
      ContinuousAt diskNormalizedQuadraticObservable data :=
    diskNormalizedQuadraticObservable_lipschitzNear_circle.eventually.mono
      (fun _ regular => regular.continuousAt)
  obtain ⟨outerRadius, outerPositive, within⟩ := Metric.eventually_nhds_iff.mp nearby
  refine ⟨outerRadius / 2, by positivity, ?_⟩
  intro curve time frequency small continuous
  have strict : dist (curve time) standardCircleBanach < outerRadius := by
    rw [dist_eq_norm]
    exact small.trans_lt (by linarith)
  have observed := (within strict).comp continuous
  have groupContinuous : ContinuousAt (fun current => diskPhysicalScaledGroup frequency (-current)) time :=
    (diskPhysicalScaledGroup_generator frequency (-time)).continuousAt.comp continuousAt_id.neg
  exact EulerNonuniqueness.General.continuousAt_operator_evaluation groupContinuous observed

end EulerNonuniqueness.Paper
