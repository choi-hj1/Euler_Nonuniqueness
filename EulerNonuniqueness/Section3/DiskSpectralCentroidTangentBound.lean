import EulerNonuniqueness.Section3.DiskPhysicalSpectralStationaryJet
import EulerNonuniqueness.Section3.ContourCentroidTangentQuadratic

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance spectralCentroidTangentC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem diskPhysicalSpectralChart_exists_quadratic_centroid_tangent_defect :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ base increment : PeriodicC1HolderHalf,
      ‖base‖ + ‖increment‖ ≤ radius →
      contourCentroidFunctional (diskPhysicalSpectralChart (base + increment)) =
        contourCentroidFunctional (diskPhysicalSpectralChart base) →
      ‖contourCentroidGaugeProjection (diskPhysicalSpectralChart base)
          (fderiv ℝ diskPhysicalSpectralChart base increment) -
        fderiv ℝ diskPhysicalSpectralChart base increment‖ ≤ constant * ‖increment‖ ^ 2 := by
  have outer : EulerNonuniqueness.General.HasLipschitzDerivativeNear contourCentroidFunctional
      (diskPhysicalSpectralChart 0) := by
    rw [diskPhysicalSpectralChart_zero]
    exact EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_analyticAt
      (analyticAt_contourCentroidFunctional _ (by simp only [sub_self, norm_zero]; norm_num))
  have composition := outer.comp diskPhysicalSpectralChart_hasLipschitzDerivativeNear
  obtain ⟨radius, positive, constant, nonnegative, tangent⟩ :=
    composition.exists_constraint_tangent_quadratic
      (fun point => contourCentroidFunctional (diskPhysicalSpectralChart point))
  have nearby : ∀ᶠ point in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖diskPhysicalSpectralChart point - standardCircleBanach‖ < 1 / 3 := by
    have chartContinuous := diskPhysicalSpectralChart_hasLipschitzDerivativeNear.lipschitzNear.continuousAt
    have limit : Tendsto diskPhysicalSpectralChart (𝓝 (0 : PeriodicC1HolderHalf))
        (𝓝 standardCircleBanach) := by
      simpa only [diskPhysicalSpectralChart_zero] using chartContinuous.tendsto
    simpa only [Metric.mem_ball, dist_eq_norm] using limit.eventually
      (Metric.ball_mem_nhds standardCircleBanach (show (0 : ℝ) < 1 / 3 by norm_num))
  obtain ⟨chartRadius, chartPositive, valid⟩ := Metric.eventually_nhds_iff.mp
    (nearby.and diskPhysicalSpectralChart_hasLipschitzDerivativeNear.1)
  refine ⟨min radius (chartRadius / 2), lt_min positive (by positivity), constant, nonnegative, ?_⟩
  intro base increment inside sameValue
  have baseSmall : dist base (0 : PeriodicC1HolderHalf) < chartRadius := by
    rw [dist_zero_right]
    have small := inside.trans (min_le_right _ _)
    linarith [norm_nonneg increment]
  obtain ⟨chartSmall, chartDerivative⟩ := valid baseSmall
  have centroidDerivative := (analyticAt_contourCentroidFunctional _ chartSmall).differentiableAt.hasFDerivAt
  have composedDerivative := HasFDerivAt.comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf) (G := ℂ) base centroidDerivative chartDerivative.hasFDerivAt
  simp only [Function.comp_def] at composedDerivative
  have bound := tangent base increment (inside.trans (min_le_left _ _)) sameValue
  rw [composedDerivative.fderiv] at bound
  have identity : contourCentroidGaugeProjection (diskPhysicalSpectralChart base)
      (fderiv ℝ diskPhysicalSpectralChart base increment) -
        fderiv ℝ diskPhysicalSpectralChart base increment =
      -c1Constant (fderiv ℝ contourCentroidFunctional (diskPhysicalSpectralChart base)
        (fderiv ℝ diskPhysicalSpectralChart base increment)) := by
    rw [contourCentroidGaugeProjection_apply]
    abel
  rw [identity, norm_neg]
  exact (c1Constant_norm_bound _).trans bound

end EulerNonuniqueness.Paper
