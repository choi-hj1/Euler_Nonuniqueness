import EulerNonuniqueness.Section3.IndependentForcingResonantRemainder
import EulerNonuniqueness.Section3.IndependentDiskRadialGenerator

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

local instance independentTangentEquationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem independentDiskPositiveProjection_embedding (direction : PeriodicC1HolderHalf) :
    independentDiskPositiveProjection (contourIndependentEmbedding direction) =
      independentPositiveMaterial (periodicHilbertPositiveProjection (diskRadialPart direction)) := by
  unfold contourIndependentEmbedding
  rw [independentDiskPositiveProjection_radial, independentFullRadial_embedding]
  rfl

theorem independentStrainForcing_spectral_tangent_resonance_zero (direction : PeriodicC1HolderHalf)
    (member : direction ∈ contourContinuousVectorSubmodule)
    (centered : (fderiv ℝ contourCentroidFunctional standardCircleBanach) direction = 0) :
    independentDiskNegativeProjection
      (independentForcingLinearCoefficient 0 (independentDiskPositiveProjection (contourIndependentEmbedding direction))) = 0 := by
  rw [independentDiskPositiveProjection_embedding, independentDiskNegativeProjection_radial]
  have zero := actualCentroidStrain_full_radial_tangent_resonance_zero direction member centered
  rw [actualCentroidStrainFullRadialBlock_eq] at zero
  unfold independentForcingFullRadialBlock EulerNonuniqueness.General.weightedOperatorBlock at zero
  simp only [ContinuousLinearMap.comp_apply] at zero
  rw [zero]
  have productZero : c1Product standardCircleBanach 0 = 0 := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change standardCircle label * 0 = 0
    exact mul_zero _
  rw [productZero, smul_zero]
  rfl

theorem independentForcingResonantCoefficient_tangent_zero (degree : ℕ) (direction : PeriodicC1HolderHalf)
    (member : direction ∈ contourContinuousVectorSubmodule)
    (centered : (fderiv ℝ contourCentroidFunctional standardCircleBanach) direction = 0) :
    independentForcingResonantCoefficient degree (contourIndependentEmbedding direction) = 0 := by
  cases degree with
  | zero =>
      rw [independentForcingResonantCoefficient_zero_degree, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.comp_apply]
      exact independentStrainForcing_spectral_tangent_resonance_zero direction member centered
  | succ degree =>
      rw [independentForcingResonantCoefficient_eq_zero (degree + 1) (by omega), ContinuousLinearMap.zero_apply]

theorem independentDiskRotatingDerivative_embedding (direction : PeriodicC1HolderHalf) :
    independentDiskRotatingDerivative (contourIndependentEmbedding direction) =
      contourIndependentEmbedding (diskRotatingDerivative direction) := by
  unfold independentDiskRotatingDerivative contourIndependentEmbedding
  with_reducible
    exact EulerNonuniqueness.General.complexPairExtension_embedding c1ConjugateCLM
      c1ConjugateCLM_complex_smul c1ConjugateCLM_involution diskRotatingDerivative direction

theorem independentForcingLinearCorrection_tangent_equation (degree : ℕ) (direction : PeriodicC1HolderHalf)
    (member : direction ∈ contourContinuousVectorSubmodule)
    (centered : (fderiv ℝ contourCentroidFunctional standardCircleBanach) direction = 0) :
    (-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2) •
        independentForcingLinearCorrection degree (contourIndependentEmbedding direction) +
      independentForcingLinearCorrection degree (contourIndependentEmbedding (diskRotatingDerivative direction)) -
      independentDiskRotatingDerivative
        (independentForcingLinearCorrection degree (contourIndependentEmbedding direction)) =
      independentForcingLinearCoefficient degree (contourIndependentEmbedding direction) := by
  have equation := congrArg (fun linear : (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ]
      PeriodicC1HolderHalf × PeriodicC1HolderHalf => linear (contourIndependentEmbedding direction))
    (independentForcingLinearCorrection_equation degree)
  simp only [EulerNonuniqueness.General.linearHomologicalOperator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    independentForcingResonantCoefficient_tangent_zero degree direction member centered, sub_zero,
    independentDiskRotatingDerivative_embedding] at equation
  exact equation

end

end EulerNonuniqueness.Paper
