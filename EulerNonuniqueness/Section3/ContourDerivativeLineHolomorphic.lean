import EulerNonuniqueness.Section3.ContourCauchySecondVariation

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem contourCauchyDirectionalDerivative_hasDerivAt_complex_line
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf) (parameter : ℂ)
    (small : ‖data + parameter • second - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    HasDerivAt (fun current : ℂ => contourCauchyDirectionalDerivative (data + current • second) first density)
      (contourCauchySecondVariation (data + parameter • second) first second density) parameter := by
  have shifted := contourCauchySecondVariation_hasDerivAt (data + parameter • second) first second density small
  have shiftedAt : HasDerivAt (fun current : ℂ =>
      contourCauchyDirectionalDerivative (data + parameter • second + current • second) first density)
      (contourCauchySecondVariation (data + parameter • second) first second density)
      (parameter - parameter) := by simpa only [sub_self] using shifted
  have inner : HasDerivAt (fun current : ℂ => current - parameter) 1 parameter :=
    (hasDerivAt_id parameter).sub_const parameter
  have translated := shiftedAt.scomp (h := fun current : ℂ => current - parameter) parameter inner
  simp only [one_smul] at translated
  convert translated using 1
  funext current
  dsimp only [Function.comp_apply]
  congr 1
  rw [sub_smul current parameter second]
  abel

end

end EulerNonuniqueness.Paper
