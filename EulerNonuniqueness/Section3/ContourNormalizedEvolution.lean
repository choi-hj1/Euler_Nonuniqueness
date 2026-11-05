import EulerNonuniqueness.Section3.ContourNormalizationDynamics

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] areaCentroidNormalizationC1Group areaCentroidNormalizationC1Semi
  areaCentroidNormalizationC1Space normalizationRegularityOperatorGroup

theorem contourAreaCentroidNormalization_exists_uniform_evolution :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {curve : ℝ → PeriodicC1HolderHalf} {time frequency : ℝ} {error : PeriodicC1HolderHalf},
      ‖curve time - standardCircleBanach‖ ≤ radius →
      HasDerivAt curve (frequency • diskEulerRotatingField (curve time) + error) time →
      contourAreaFunctional (contourAreaCentroidNormalization (curve time)) = Real.pi ∧
      contourCentroidFunctional (contourAreaCentroidNormalization (curve time)) = 0 ∧
      HasDerivAt (contourAreaCentroidNormalization ∘ curve)
        (frequency • diskEulerRotatingField (contourAreaCentroidNormalization (curve time)) +
          fderiv ℝ contourAreaCentroidNormalization (curve time) error) time ∧
      ‖fderiv ℝ contourAreaCentroidNormalization (curve time) error‖ ≤ constant * ‖error‖ := by
  obtain ⟨derivativeRadius, derivativePositive, constant, constantOne, derivativeBounds, _, _⟩ :=
    contourAreaCentroidNormalization_exists_uniform_bounds
  obtain ⟨admissibleRadius, admissiblePositive, admissible⟩ :=
    Metric.eventually_nhds_iff.mp contourAreaCentroidNormalization_eventually_admissible
  let radius := min derivativeRadius (admissibleRadius / 2)
  refine ⟨radius, by dsimp [radius]; positivity, constant, constantOne, ?_⟩
  intro curve time frequency error small derivative
  have strict : dist (curve time) standardCircleBanach < admissibleRadius := by
    rw [dist_eq_norm]
    exact (small.trans (min_le_right _ _)).trans_lt (by linarith)
  obtain ⟨rawSmall, positiveArea, centeredSmall, normalizedSmall⟩ := admissible strict
  refine ⟨contourAreaCentroidNormalization_area _ positiveArea,
    contourAreaCentroidNormalization_centroid _ positiveArea,
    contourAreaCentroidNormalization_curve_hasDerivAt curve time frequency error derivative rawSmall centeredSmall normalizedSmall, ?_⟩
  exact ((fderiv ℝ contourAreaCentroidNormalization (curve time)).le_opNorm error).trans
    (mul_le_mul_of_nonneg_right (derivativeBounds _ (small.trans (min_le_left _ _))) (norm_nonneg _))

end EulerNonuniqueness.Paper
