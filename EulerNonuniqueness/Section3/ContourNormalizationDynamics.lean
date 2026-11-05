import EulerNonuniqueness.Section3.ContourNormalizationSelfConjugacy
import EulerNonuniqueness.Section3.ContourNormalizationRegularity

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] areaCentroidNormalizationC1Group areaCentroidNormalizationC1Semi
  areaCentroidNormalizationC1Space normalizationRegularityOperatorGroup

theorem contourAreaCentroidNormalization_curve_hasDerivAt
    (curve : ℝ → PeriodicC1HolderHalf) (time frequency : ℝ) (error : PeriodicC1HolderHalf)
    (derivative : HasDerivAt curve (frequency • diskEulerRotatingField (curve time) + error) time)
    (small : ‖curve time - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi)))
    (centeredSmall : ‖contourCentroidRecenter (curve time) - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (normalizedSmall : ‖contourAreaCentroidNormalization (curve time) - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    HasDerivAt (contourAreaCentroidNormalization ∘ curve)
      (frequency • diskEulerRotatingField (contourAreaCentroidNormalization (curve time)) +
        fderiv ℝ contourAreaCentroidNormalization (curve time) error) time := by
  have chain := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := PeriodicC1HolderHalf) (E := PeriodicC1HolderHalf)
    (f := curve) time
    (contourAreaCentroidNormalization_differentiableAt (curve time) (small.trans_le (min_le_left _ _))).hasFDerivAt derivative
  rw [map_add, map_smul, contourAreaCentroidNormalization_derivative_self (curve time) small centeredSmall normalizedSmall] at chain
  exact chain

theorem contourAreaCentroidNormalization_exists_uniform_recovery :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ data correction : PeriodicC1HolderHalf,
      ‖data - standardCircleBanach‖ + ‖correction‖ ≤ radius →
      contourAreaFunctional data = Real.pi → contourCentroidFunctional data = 0 →
      ‖contourAreaCentroidNormalization (data - correction) - data‖ ≤ constant * ‖correction‖ ∧
      ∀ error : PeriodicC1HolderHalf,
        ‖fderiv ℝ contourAreaCentroidNormalization (data - correction) error‖ ≤ constant * ‖error‖ := by
  obtain ⟨radius, positive, constant, one, derivativeBounds, differenceBounds, _⟩ :=
    contourAreaCentroidNormalization_exists_uniform_bounds
  refine ⟨radius, positive, constant, one, ?_⟩
  intro data correction inside area centered
  have originalSmall : ‖data - standardCircleBanach‖ ≤ radius := by linarith [norm_nonneg correction]
  have shiftedSmall : ‖data - correction - standardCircleBanach‖ ≤ radius := by
    rw [show data - correction - standardCircleBanach = (data - standardCircleBanach) - correction by abel]
    exact (norm_sub_le _ _).trans inside
  constructor
  · have actual := differenceBounds (data - correction) data shiftedSmall originalSmall
    rw [contourAreaCentroidNormalization_fixes_constraints data area centered] at actual
    have difference : data - correction - data = -correction := by abel
    simpa only [difference, norm_neg] using actual
  · intro error
    exact ((fderiv ℝ contourAreaCentroidNormalization (data - correction)).le_opNorm error).trans
      (mul_le_mul_of_nonneg_right (derivativeBounds (data - correction) shiftedSmall) (norm_nonneg _))

end EulerNonuniqueness.Paper
