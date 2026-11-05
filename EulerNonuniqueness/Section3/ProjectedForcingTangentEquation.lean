import EulerNonuniqueness.Section3.IndependentForcingTangentEquation
import EulerNonuniqueness.Section3.ContourCentroidSpectralProjection
import EulerNonuniqueness.Section3.ContourContinuousGauge
import EulerNonuniqueness.Section3.ContourCentroidTangentQuadratic

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentTangentEquationC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

def projectedIndependentForcingLinearCorrection (degree : ℕ) (direction : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  independentForcingLinearCorrection degree
    (contourIndependentEmbedding (contourCentroidGaugeProjection standardCircleBanach direction))

theorem projectedIndependentForcingLinearCorrection_equation (degree : ℕ) (direction : PeriodicC1HolderHalf)
    (member : direction ∈ contourContinuousVectorSubmodule) :
    (-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2) • projectedIndependentForcingLinearCorrection degree direction +
      projectedIndependentForcingLinearCorrection degree (diskRotatingDerivative direction) -
      independentDiskRotatingDerivative (projectedIndependentForcingLinearCorrection degree direction) =
      independentForcingLinearCoefficient degree
        (contourIndependentEmbedding (contourCentroidGaugeProjection standardCircleBanach direction)) := by
  with_reducible_and_instances
    have tangentMember := contourContinuousVectorSubmodule_centroid_projection standardCircleBanach direction member
    have tangentZero := contourCentroidGaugeProjection_centroid_zero standardCircleBanach direction
      (by simp)
    have equation := independentForcingLinearCorrection_tangent_equation degree
      (contourCentroidGaugeProjection standardCircleBanach direction) tangentMember tangentZero
    have commutes := DFunLike.congr_fun contourCentroidGaugeProjection_circle_commutes direction
    simp only [ContinuousLinearMap.comp_apply] at commutes
    simpa only [projectedIndependentForcingLinearCorrection, commutes] using equation

theorem projectedIndependentForcingLinearCorrection_equation_with_defect (degree : ℕ)
    (direction : PeriodicC1HolderHalf) (member : direction ∈ contourContinuousVectorSubmodule) :
    (-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2) • projectedIndependentForcingLinearCorrection degree direction +
      projectedIndependentForcingLinearCorrection degree (diskRotatingDerivative direction) -
      independentDiskRotatingDerivative (projectedIndependentForcingLinearCorrection degree direction) =
      independentForcingLinearCoefficient degree (contourIndependentEmbedding direction) -
        independentForcingLinearCoefficient degree (contourIndependentEmbedding
          (direction - contourCentroidGaugeProjection standardCircleBanach direction)) := by
  rw [projectedIndependentForcingLinearCorrection_equation degree direction member, map_sub, map_sub]
  abel

theorem projectedForcing_exists_uniform_quadratic_centroid_defect :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ (degree : ℕ) (direction : PeriodicC1HolderHalf),
      ‖direction‖ ≤ radius → contourCentroidFunctional (standardCircleBanach + direction) = 0 →
      ‖independentForcingLinearCoefficient degree (contourIndependentEmbedding
        (direction - contourCentroidGaugeProjection standardCircleBanach direction))‖ ≤
        constant * ‖independentForcingLinearCoefficient degree‖ * ‖direction‖ ^ 2 := by
  obtain ⟨radius, positive, constant, nonnegative, deviation⟩ :=
    contourCentroidGaugeProjection_exists_uniform_quadratic_deviation
  refine ⟨radius, positive, constant, nonnegative, ?_⟩
  intro degree direction inside centered
  have bound := deviation standardCircleBanach direction
    (by simpa only [sub_self, norm_zero, zero_add] using inside)
    (by simpa only [contourCentroidFunctional_standardCircle_zero] using centered)
  rw [norm_sub_rev] at bound
  have embedding : ‖contourIndependentEmbedding
      (direction - contourCentroidGaugeProjection standardCircleBanach direction)‖ ≤
      ‖direction - contourCentroidGaugeProjection standardCircleBanach direction‖ := by
    change max ‖direction - contourCentroidGaugeProjection standardCircleBanach direction‖
      ‖c1Conjugate (direction - contourCentroidGaugeProjection standardCircleBanach direction)‖ ≤ _
    exact max_le le_rfl (c1Conjugate_norm_bound _)
  calc
    _ ≤ ‖independentForcingLinearCoefficient degree‖ *
        ‖contourIndependentEmbedding (direction - contourCentroidGaugeProjection standardCircleBanach direction)‖ :=
      (independentForcingLinearCoefficient degree).le_opNorm _
    _ ≤ ‖independentForcingLinearCoefficient degree‖ * (constant * ‖direction‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (embedding.trans bound) (norm_nonneg _)
    _ = _ := by ring

end

end EulerNonuniqueness.Paper
