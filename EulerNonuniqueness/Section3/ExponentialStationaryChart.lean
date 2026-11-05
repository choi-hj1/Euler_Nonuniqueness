import Mathlib

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

def exponentialStationaryChart (generator : Space →L[ℝ] Space →L[ℝ] Space)
    (base : Space) (increment : Space) : Space :=
  (NormedSpace.exp ℝ (generator increment)) (base + increment - generator increment base)

theorem exponentialStationaryChart_zero (generator : Space →L[ℝ] Space →L[ℝ] Space)
    (base : Space) : exponentialStationaryChart generator base 0 = base := by
  simp [exponentialStationaryChart]

theorem exponentialStationaryChart_analyticAt (generator : Space →L[ℝ] Space →L[ℝ] Space)
    (base point : Space) : AnalyticAt ℝ (exponentialStationaryChart generator base) point := by
  have operator : AnalyticAt ℝ (fun increment : Space => NormedSpace.exp ℝ (generator increment)) point :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) (generator point)).comp (generator.analyticAt point)
  have evaluation : AnalyticAt ℝ (fun increment : Space => generator increment base) point :=
    ((ContinuousLinearMap.apply ℝ Space base).comp generator).analyticAt point
  have vector : AnalyticAt ℝ (fun increment : Space => base + increment - generator increment base) point :=
    (analyticAt_const.fun_add ((ContinuousLinearMap.id ℝ Space).analyticAt point)).fun_sub evaluation
  exact (ContinuousLinearMap.apply ℝ Space).flip.analyticAt_bilinear
    (NormedSpace.exp ℝ (generator point), base + point - generator point base) |>.comp₂ operator vector

theorem exponentialStationaryChart_hasFDerivAt_zero (generator : Space →L[ℝ] Space →L[ℝ] Space)
    (base : Space) :
    HasFDerivAt (exponentialStationaryChart generator base) (ContinuousLinearMap.id ℝ Space) 0 := by
  have operator : HasFDerivAt (fun increment : Space => NormedSpace.exp ℝ (generator increment)) generator 0 := by
    have exponential : HasFDerivAt (NormedSpace.exp ℝ)
        (ContinuousLinearMap.id ℝ (Space →L[ℝ] Space)) (generator 0) := by
      simpa only [map_zero, ContinuousLinearMap.one_def] using
        (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Space →L[ℝ] Space))
    have derivative := HasFDerivAt.comp (𝕜 := ℝ) (E := Space)
      (F := Space →L[ℝ] Space) (G := Space →L[ℝ] Space)
      (0 : Space) exponential generator.hasFDerivAt
    simpa only [map_zero, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] using derivative
  let evaluation : Space →L[ℝ] Space := (ContinuousLinearMap.apply ℝ Space base).comp generator
  have vector : HasFDerivAt (fun increment : Space => base + increment - generator increment base)
      (ContinuousLinearMap.id ℝ Space - evaluation) 0 := by
    simpa only [zero_add, id_eq, evaluation, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply] using
      ((hasFDerivAt_const base (0 : Space)).add (hasFDerivAt_id (0 : Space))).sub evaluation.hasFDerivAt
  have actual := operator.clm_apply vector
  have derivative : (NormedSpace.exp ℝ (generator 0)).comp
        (ContinuousLinearMap.id ℝ Space - evaluation) + generator.flip
          (base + 0 - generator 0 base) = ContinuousLinearMap.id ℝ Space := by
    ext increment
    simp [evaluation]
  rw [derivative] at actual
  exact actual

theorem exponentialStationaryChart_hasStrictFDerivAt_zero
    (generator : Space →L[ℝ] Space →L[ℝ] Space) (base : Space) :
    HasStrictFDerivAt (exponentialStationaryChart generator base) (ContinuousLinearMap.id ℝ Space) 0 := by
  have analytic := exponentialStationaryChart_analyticAt generator base 0
  simpa only [(exponentialStationaryChart_hasFDerivAt_zero generator base).fderiv] using
    analytic.hasStrictFDerivAt

end

end EulerNonuniqueness.General
