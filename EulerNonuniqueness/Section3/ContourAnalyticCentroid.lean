import EulerNonuniqueness.Section3.ContourAnalyticArea
import EulerNonuniqueness.Section3.ContourAnalyticFirstMoment

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

def contourCentroidFunctional (data : PeriodicC1HolderHalf) : ℂ :=
  contourPolynomialMoment 1 data / (contourAreaFunctional data : ℂ)

theorem contourAreaFunctional_pos (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) : 0 < contourAreaFunctional data := by
  rw [contourAreaFunctional_eq_domain_area data small]
  have positive : 0 < volume (nearCircleInterior data small) :=
    IsOpen.measure_pos volume (nearCircleInterior_isOpen data small) ⟨0, nearCircleInterior_zero_mem data small⟩
  have finite : volume (nearCircleInterior data small) < ⊤ := (nearCircleInterior_isBounded data small).measure_lt_top
  exact ENNReal.toReal_pos positive.ne' finite.ne

theorem analyticAt_contourCentroidFunctional (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) : AnalyticAt ℝ contourCentroidFunctional data := by
  have denominator := (Complex.ofRealCLM.analyticAt (x := contourAreaFunctional data)).comp
    (f := contourAreaFunctional) (analyticAt_contourAreaFunctional data)
  have nonzero : (contourAreaFunctional data : ℂ) ≠ 0 := by
    exact_mod_cast (contourAreaFunctional_pos data small).ne'
  exact (analyticAt_contourPolynomialMoment 1 data).fun_div denominator nonzero

theorem contourCentroidFunctional_eq_domain_centroid (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    contourCentroidFunctional data = (∫ position in nearCircleInterior data small, position) /
      ((volume (nearCircleInterior data small)).toReal : ℂ) := by
  rw [contourCentroidFunctional, contourPolynomialMoment_one_eq_domain_integral data small,
    contourAreaFunctional_eq_domain_area data small]

end

end EulerNonuniqueness.Paper
