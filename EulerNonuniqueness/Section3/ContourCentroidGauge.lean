import EulerNonuniqueness.Section3.ContourCentroidTranslation
import Mathlib.Analysis.Calculus.ContDiff.Basic

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

local instance centroidGaugeHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph

local instance centroidGaugeC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

local instance centroidGaugeOperatorGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem contourCentroidFunctional_derivative_constant (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    (fderiv ℝ contourCentroidFunctional data).comp c1ConstantCLM = ContinuousLinearMap.id ℝ ℂ := by
  have centroidDerivative : HasFDerivAt contourCentroidFunctional
      (fderiv ℝ contourCentroidFunctional data) data :=
    (analyticAt_contourCentroidFunctional data small).differentiableAt.hasFDerivAt
  have translationDerivative : HasFDerivAt (fun translation : ℂ => data + c1ConstantCLM translation)
      c1ConstantCLM 0 := by
    simpa only [zero_add] using (hasFDerivAt_const (𝕜 := ℝ) data (0 : ℂ)).add c1ConstantCLM.hasFDerivAt
  have composite : HasFDerivAt (fun translation : ℂ => contourCentroidFunctional (data + c1ConstantCLM translation))
      ((fderiv ℝ contourCentroidFunctional data).comp c1ConstantCLM) 0 := by
    have atTranslated : HasFDerivAt contourCentroidFunctional
        (fderiv ℝ contourCentroidFunctional data) (data + c1ConstantCLM 0) := by
      simpa only [map_zero, add_zero] using centroidDerivative
    simpa only [Function.comp_def] using HasFDerivAt.comp (𝕜 := ℝ) (E := ℂ)
      (F := PeriodicC1HolderHalf) (G := ℂ) (0 : ℂ) atTranslated translationDerivative
  have identity : (fun translation : ℂ => contourCentroidFunctional (data + c1ConstantCLM translation)) =
      fun translation : ℂ => contourCentroidFunctional data + translation := by
    funext translation
    exact contourCentroidFunctional_translate data translation (contourAreaFunctional_pos data small).ne'
  rw [identity] at composite
  have expected : HasFDerivAt (fun translation : ℂ => contourCentroidFunctional data + translation)
      (ContinuousLinearMap.id ℝ ℂ) 0 := by
    simpa only [zero_add] using (hasFDerivAt_const (𝕜 := ℝ) (contourCentroidFunctional data) (0 : ℂ)).add
      (hasFDerivAt_id (𝕜 := ℝ) (0 : ℂ))
  exact composite.unique expected

def contourCentroidGaugeProjection (data : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  ContinuousLinearMap.id ℝ PeriodicC1HolderHalf - c1ConstantCLM.comp (fderiv ℝ contourCentroidFunctional data)

theorem contourCentroidGaugeProjection_apply (data direction : PeriodicC1HolderHalf) :
    contourCentroidGaugeProjection data direction = direction -
      c1Constant ((fderiv ℝ contourCentroidFunctional data) direction) := rfl

theorem contourCentroidGaugeProjection_centroid_zero (data direction : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    (fderiv ℝ contourCentroidFunctional data) (contourCentroidGaugeProjection data direction) = 0 := by
  rw [contourCentroidGaugeProjection_apply]
  rw [(fderiv ℝ contourCentroidFunctional data).map_sub direction
    (c1Constant ((fderiv ℝ contourCentroidFunctional data) direction))]
  have identity := DFunLike.congr_fun (contourCentroidFunctional_derivative_constant data small)
    ((fderiv ℝ contourCentroidFunctional data) direction)
  change (fderiv ℝ contourCentroidFunctional data) (c1Constant ((fderiv ℝ contourCentroidFunctional data) direction)) =
    (fderiv ℝ contourCentroidFunctional data) direction at identity
  rw [identity, sub_self]

theorem contourCentroidGaugeProjection_idempotent (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    (contourCentroidGaugeProjection data).comp (contourCentroidGaugeProjection data) =
      contourCentroidGaugeProjection data := by
  apply ContinuousLinearMap.ext
  intro direction
  change contourCentroidGaugeProjection data (contourCentroidGaugeProjection data direction) = _
  rw [contourCentroidGaugeProjection_apply, contourCentroidGaugeProjection_centroid_zero data direction small]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (contourCentroidGaugeProjection data direction).val.1 label - 0 = _
  exact sub_zero _

end EulerNonuniqueness.Paper
