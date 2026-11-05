import EulerNonuniqueness.Section3.ContourVelocitySecondFrechet
import EulerNonuniqueness.Section3.RelabeledDiskPeriodFamily

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter Set Metric
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance relabelContinuityC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance relabelContinuityOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance relabelContinuityOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem relabeledDiskDerivative_exists_continuousOn (angular : PeriodicC1HolderHalf) :
    ∃ radius > 0, ContinuousOn (fun parameter : ℝ => relabeledDiskDerivative (parameter • angular))
      (Icc (-radius) radius) := by
  have curveContinuous : Continuous (diskRelabelCurve angular) :=
    continuous_iff_continuousAt.mpr (fun parameter => (diskRelabelCurve_analyticAt angular parameter).continuousAt)
  have curveLimit : Tendsto (diskRelabelCurve angular) (𝓝 (0 : ℝ)) (𝓝 standardCircleBanach) := by
    simpa only [diskRelabelCurve_zero] using curveContinuous.tendsto 0
  have threshold : (0 : ℝ) < min 1 (2 / (3 * Real.pi)) := by positivity
  have inside : ∀ᶠ parameter in 𝓝 (0 : ℝ),
      diskRelabelCurve angular parameter ∈ ball standardCircleBanach (min 1 (2 / (3 * Real.pi))) :=
    curveLimit.eventually (ball_mem_nhds standardCircleBanach threshold)
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp inside
  have maps : MapsTo (diskRelabelCurve angular) (Icc (-(radius / 2)) (radius / 2))
      (ball standardCircleBanach (min 1 (2 / (3 * Real.pi)))) := by
    intro parameter member
    apply contained
    rw [mem_ball_zero_iff, Real.norm_eq_abs]
    exact (abs_le.mpr member).trans_lt (by linarith)
  have actual := continuousOn_fderiv_extendedContourVelocity.comp curveContinuous.continuousOn maps
  refine ⟨radius / 2, by positivity, ?_⟩
  change ContinuousOn (fun parameter : ℝ => fderiv ℝ extendedContourVelocity
    (diskRelabelCurve (parameter • angular) 1) - c1ProductCLM (c1Constant (Complex.I / 2))) _
  simp_rw [diskRelabelCurve_real_smul]
  exact actual.sub continuous_const.continuousOn

end

end EulerNonuniqueness.Paper
