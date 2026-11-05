import EulerNonuniqueness.Section3.MovingContourConfinementTube
import EulerNonuniqueness.Section3.DiskNeutralContinuousVectors
import EulerNonuniqueness.Section3.RelabeledDiskForcingAnalytic
import EulerNonuniqueness.Section3.CanonicalInteractionInitialBound

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] normalizedUniformSlopeC1Group chartedBilinearC1Space
  canonicalForcingAddCommGroup canonicalForcingAdd canonicalForcingZero canonicalForcingNeg canonicalForcingSub

theorem exists_contour_confinement_shape_monitor_radius {budget : ℝ} (budgetPositive : 0 < budget) :
    ∃ radius > 0, radius ≤ budget ∧ ∀ data : PeriodicC1HolderHalf,
      ‖data - standardCircleBanach‖ < radius → data ∈ contourContinuousVectorSubmodule →
      let angular := diskNeutralCLM (diskPhysicalSpectralCoordinate data)
      ‖angular‖ < budget ∧
      ‖diskRelabelCurve angular 1 - standardCircleBanach‖ + ‖data - diskRelabelCurve angular 1‖ ≤ budget ∧
      angular ∈ contourContinuousVectorSubmodule ∧
      data - diskRelabelCurve angular 1 ∈ contourContinuousVectorSubmodule := by
  have angularContinuous : ContinuousAt
      (fun data => diskNeutralCLM (diskPhysicalSpectralCoordinate data)) standardCircleBanach :=
    diskNeutralCLM.continuous.continuousAt.comp diskPhysicalSpectralCoordinate_continuousAt_circle
  have angularZero : diskNeutralCLM (diskPhysicalSpectralCoordinate standardCircleBanach) = 0 := by
    rw [diskPhysicalSpectralCoordinate_circle, map_zero]
  have relabelContinuous : ContinuousAt
      (fun data => diskRelabelCurve (diskNeutralCLM (diskPhysicalSpectralCoordinate data)) 1)
      standardCircleBanach := by
    exact ContinuousAt.comp (g := fun angular => diskRelabelCurve angular 1)
      (f := fun data => diskNeutralCLM (diskPhysicalSpectralCoordinate data))
      (diskRelabelMap_analyticAt _).continuousAt angularContinuous
  have relabelZero : diskRelabelCurve (diskNeutralCLM (diskPhysicalSpectralCoordinate standardCircleBanach)) 1 =
      standardCircleBanach := by rw [angularZero, diskRelabelCurve_zero_angular]
  have angularNear : ∀ᶠ data in 𝓝 standardCircleBanach,
      ‖diskNeutralCLM (diskPhysicalSpectralCoordinate data)‖ < budget := by
    have convergence : Tendsto (fun data => ‖diskNeutralCLM (diskPhysicalSpectralCoordinate data)‖)
        (𝓝 standardCircleBanach) (𝓝 (0 : ℝ)) := by
      simpa only [angularZero, norm_zero] using angularContinuous.norm.tendsto
    exact convergence.eventually (eventually_lt_nhds budgetPositive)
  have splitContinuous : ContinuousAt
      (fun data => ‖diskRelabelCurve (diskNeutralCLM (diskPhysicalSpectralCoordinate data)) 1 - standardCircleBanach‖ +
        ‖data - diskRelabelCurve (diskNeutralCLM (diskPhysicalSpectralCoordinate data)) 1‖) standardCircleBanach :=
    ((relabelContinuous.sub continuousAt_const).norm).add ((continuousAt_id.sub relabelContinuous).norm)
  have splitNear : ∀ᶠ data in 𝓝 standardCircleBanach,
      ‖diskRelabelCurve (diskNeutralCLM (diskPhysicalSpectralCoordinate data)) 1 - standardCircleBanach‖ +
        ‖data - diskRelabelCurve (diskNeutralCLM (diskPhysicalSpectralCoordinate data)) 1‖ < budget := by
    have convergence : Tendsto
        (fun data => ‖diskRelabelCurve (diskNeutralCLM (diskPhysicalSpectralCoordinate data)) 1 - standardCircleBanach‖ +
          ‖data - diskRelabelCurve (diskNeutralCLM (diskPhysicalSpectralCoordinate data)) 1‖)
        (𝓝 standardCircleBanach) (𝓝 (0 : ℝ)) := by
      simpa only [relabelZero, sub_self, norm_zero, zero_add] using splitContinuous.tendsto
    exact convergence.eventually (eventually_lt_nhds budgetPositive)
  obtain ⟨outer, outerPositive, contained⟩ := Metric.eventually_nhds_iff.mp
    (angularNear.and (splitNear.and diskPhysicalSpectralCoordinate_eventually_continuousVector))
  refine ⟨min outer budget, lt_min outerPositive budgetPositive, min_le_right _ _, ?_⟩
  intro data nearby member
  have valid := contained (by simpa only [dist_eq_norm] using nearby.trans_le (min_le_left _ _))
  have coordinateMember := valid.2.2 member
  have angularMember := diskNeutralCLM_mem_contourContinuousVectorSubmodule _ coordinateMember
  have relabelMember := diskStationaryNeutral_mem_contourContinuousVectorSubmodule _ coordinateMember
  rw [diskRelabelNeutralCLM_apply, diskStationaryChart_relabel _ (diskNeutralCLM_real _)] at relabelMember
  exact ⟨valid.1, valid.2.1.le, angularMember, contourContinuousVectorSubmodule.sub_mem member relabelMember⟩

end EulerNonuniqueness.Paper
