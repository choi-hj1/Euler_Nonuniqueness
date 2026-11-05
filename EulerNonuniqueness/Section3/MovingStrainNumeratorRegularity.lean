import EulerNonuniqueness.General.ForcingNumeratorRealRegularity
import EulerNonuniqueness.Section3.MovingStrainDerivativeRegularity
import EulerNonuniqueness.Section3.MovingStrainQuadraticRegularity

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] movingStrainGeneratorC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityBilinearGroup secondIdentityBilinearModule secondLipschitzBilinearSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace
  movingStrainPairBilinearGroup movingStrainPairBilinearSpace

local instance movingNumeratorRealOperatorSpace : NormedSpace ℝ
    ((PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf × PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf × PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℂ)

local instance movingNumeratorRealBilinearSpace : NormedSpace ℝ
    ((PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ]
      (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf × PeriodicC1HolderHalf)
    (F := (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ]
      PeriodicC1HolderHalf × PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℂ)

local instance movingNumeratorInnerSpace : NormedSpace ℝ
    (((PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ]
      (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf) ×
      (PeriodicC1HolderHalf × PeriodicC1HolderHalf)) :=
  Prod.normedSpace

local instance movingNumeratorTupleSpace : NormedSpace ℝ
    (((PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf) ×
      (((PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ]
        (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf) ×
        (PeriodicC1HolderHalf × PeriodicC1HolderHalf))) :=
  Prod.normedSpace

theorem independentStrainPrimitiveAt_lipschitzNear :
    EulerNonuniqueness.General.LipschitzNear independentStrainPrimitiveAt standardCircleBanach := by
  let primitiveMap : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
    ((c1ProductCLM (c1Constant (diskForcingPrimitiveFactor 0 1))).comp c1ConjugateCLM).prod 0
  have identity : (primitiveMap : PeriodicC1HolderHalf → PeriodicC1HolderHalf × PeriodicC1HolderHalf) =
      independentStrainPrimitiveAt := by
    funext data
    apply Prod.ext
    · apply PeriodicC1HolderHalf.ext_value
      intro label
      rfl
    · rfl
  rw [← identity]
  exact ⟨_, Set.univ, Filter.univ_mem, primitiveMap.lipschitz.lipschitzOnWith⟩

theorem independentCentroidStrainNumeratorAt_lipschitzNear :
    EulerNonuniqueness.General.LipschitzNear
      (fun data => independentCentroidStrainNumeratorAt data (independentStrainPrimitiveAt data))
      standardCircleBanach := by
  have inner := independentCentroidStrainDerivativeAt_lipschitzNear.prodMk
    (contourIndependentQuadraticAt_lipschitzNear.prodMk independentStrainPrimitiveAt_lipschitzNear)
  have outer := EulerNonuniqueness.General.forcingLinearCoefficient_lipschitzNear
    (Space := PeriodicC1HolderHalf × PeriodicC1HolderHalf)
    (independentCentroidStrainDerivativeAt standardCircleBanach,
      (contourIndependentQuadraticAt standardCircleBanach, independentStrainPrimitiveAt standardCircleBanach))
  unfold independentCentroidStrainNumeratorAt
  with_reducible_and_instances
    exact EulerNonuniqueness.General.LipschitzNear.comp
      (inner := fun data => (independentCentroidStrainDerivativeAt data,
        (contourIndependentQuadraticAt data, independentStrainPrimitiveAt data)))
      (point := standardCircleBanach) outer inner

end EulerNonuniqueness.Paper
