import EulerNonuniqueness.Section3.ContourGaugeOperatorSecondRegularity

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] centroidGaugeRegularityC1Space centroidGaugeRegularityDerivativeGroup
  centroidGaugeRegularityDerivativeSpace centroidGaugeRegularityOperatorGroup
  centroidGaugeRegularityConstantGroup gaugeOperatorTaylorConstantSpace gaugeOperatorTaylorOperatorSpace

local instance strainSourceC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

local instance strainSourceCoefficientDerivativeGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] ℂ →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := ℂ →L[ℝ] PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

local instance strainSourceCoefficientDerivativeSpace : NormedSpace ℝ
    (PeriodicC1HolderHalf →L[ℝ] ℂ →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := ℂ →L[ℝ] PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

def c1ConjugateCoefficientCLM : PeriodicC1HolderHalf →L[ℝ] ℂ →L[ℝ] PeriodicC1HolderHalf :=
  ((ContinuousLinearMap.compL ℝ ℂ PeriodicC1HolderHalf PeriodicC1HolderHalf).flip c1ConstantCLM).comp
    (c1ProductCLM.comp c1ConjugateCLM)

theorem c1ConjugateCoefficientCLM_apply (data : PeriodicC1HolderHalf) (coefficient : ℂ) :
    c1ConjugateCoefficientCLM data coefficient = c1Product (c1Conjugate data) (c1Constant coefficient) := rfl

def contourStrainSourceCoefficient (data : PeriodicC1HolderHalf) : ℂ →L[ℝ] PeriodicC1HolderHalf :=
  (contourCentroidGaugeProjection data).comp (c1ConjugateCoefficientCLM data)

theorem contourStrainSourceCoefficient_apply (data : PeriodicC1HolderHalf) (coefficient : ℂ) :
    contourStrainSourceCoefficient data coefficient =
      contourCentroidGaugeProjection data (c1Product (c1Conjugate data) (c1Constant coefficient)) := rfl

theorem contourStrainSourceCoefficient_contDiffAt_three :
    ContDiffAt ℝ 3 contourStrainSourceCoefficient standardCircleBanach := by
  have first := contourCentroidGaugeProjection_contDiffAt_three
  have second : ContDiffAt ℝ 3 (fun data : PeriodicC1HolderHalf => c1ConjugateCoefficientCLM data)
      standardCircleBanach := c1ConjugateCoefficientCLM.contDiff.contDiffAt
  unfold contourStrainSourceCoefficient
  with_reducible_and_instances
    exact ContDiffAt.clm_comp (𝕜 := ℝ) (X := PeriodicC1HolderHalf)
      (E := ℂ) (F := PeriodicC1HolderHalf) (G := PeriodicC1HolderHalf) first second

end EulerNonuniqueness.Paper
