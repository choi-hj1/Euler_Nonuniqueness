import EulerNonuniqueness.General.HomologicalJetCoordinates

noncomputable section

namespace EulerNonuniqueness.General

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

local instance coordinateJetOperatorRing : NormedRing (Space →L[ℝ] Space) :=
  ContinuousLinearMap.toNormedRing (𝕜 := ℝ) (E := Space)
local instance coordinateJetOperatorAlgebra : NormedAlgebra ℝ (Space →L[ℝ] Space) :=
  ContinuousLinearMap.toNormedAlgebra (𝕜 := ℝ) (E := Space)

theorem hasFDerivAt_coordinate_vector_field
    (chartFunction field : Space → Space) (base : Space) (chart : Space ≃L[ℝ] Space)
    (chartSecond : BilinearEnd Space) (fieldLinear : Space →L[ℝ] Space)
    (chartDerivative : HasFDerivAt chartFunction chart.toContinuousLinearMap base)
    (chartSecondDerivative : HasFDerivAt (fderiv ℝ chartFunction) chartSecond base)
    (fieldDerivative : HasFDerivAt field fieldLinear (chartFunction base)) :
    HasFDerivAt
      (fun current => Ring.inverse (fderiv ℝ chartFunction current) (field (chartFunction current)))
      (chart.symm.toContinuousLinearMap.comp
        (fieldLinear.comp chart.toContinuousLinearMap - chartSecond.flip (chart.symm (field (chartFunction base)))))
      base := by
  let inverseJet : (Space →L[ℝ] Space) →L[ℝ] Space →L[ℝ] Space :=
    -ContinuousLinearMap.mulLeftRight ℝ (Space →L[ℝ] Space)
      chart.symm.toContinuousLinearMap chart.symm.toContinuousLinearMap
  have inverseDerivative : HasFDerivAt Ring.inverse inverseJet (fderiv ℝ chartFunction base) := by
    rw [chartDerivative.fderiv]
    exact hasFDerivAt_ringInverse (𝕜 := ℝ) chart.toUnit
  have inverseIdentity : Ring.inverse chart.toContinuousLinearMap = chart.symm.toContinuousLinearMap :=
    Ring.inverse_unit chart.toUnit
  have inverseComposed := inverseDerivative.comp base chartSecondDerivative
  have fieldComposed := fieldDerivative.comp base chartDerivative
  have actual := inverseComposed.clm_apply fieldComposed
  simp only [Function.comp_def] at actual
  have derivativeIdentity :
      (Ring.inverse (fderiv ℝ chartFunction base)).comp
          (fieldLinear.comp chart.toContinuousLinearMap) +
        (inverseJet.comp chartSecond).flip (field (chartFunction base)) =
      chart.symm.toContinuousLinearMap.comp
        (fieldLinear.comp chart.toContinuousLinearMap -
          chartSecond.flip (chart.symm (field (chartFunction base)))) := by
    rw [chartDerivative.fderiv, inverseIdentity]
    apply ContinuousLinearMap.ext
    intro direction
    simp only [inverseJet, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.sub_apply, map_sub]
    abel
  rw [derivativeIdentity] at actual
  exact actual

end EulerNonuniqueness.General
