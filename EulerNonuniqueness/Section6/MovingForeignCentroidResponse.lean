import EulerNonuniqueness.Section3.ExteriorCentroidDomainAverage
import EulerNonuniqueness.Section6.MovingPatchSubfamilyMoments
import EulerNonuniqueness.Section6.MovingExteriorCoefficientBound
import EulerNonuniqueness.Section6.MovingForeignQuadrupole
import EulerNonuniqueness.Section6.PaperPatchCentroidAlgebra
import EulerNonuniqueness.Section3.MovingMaterialCentroidGeometry

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem subfamily_biotSavart_continuous {count : ℕ} (family : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) (time : ℝ) :
    Continuous (biotSavart (family.subfamilyVorticity selected time)) := by
  apply continuous_biotSavart_of_memLp_support holderConjugate_four_fourThirds
    (family.subfamilyVorticity_memLp selected time (ENNReal.ofReal (4 : ℝ))) (by norm_num)
    (show 0 ≤ ∑ index : Fin count, (‖(family.patch index).center time‖ + 2 * (family.patch index).radius) from
      Finset.sum_nonneg fun index _ => add_nonneg (norm_nonneg _)
        (mul_nonneg (by norm_num) (family.patch index).radius_positive.le))
  exact family.subfamilyVorticity_support selected time

theorem subfamily_average_defect_eq_centroid_response {count : ℕ}
    (family : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (receiver : MovingMaterialPatch) (time : ℝ) {distance : ℝ}
    (distancePositive : 0 < distance)
    (separated : ∀ source ∈ selected, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖receiver.center time - position‖)
    (smallRadius : 24 * receiver.radius / distance < 1)
    (area : contourAreaFunctional (receiver.shape time) = Real.pi) :
    (Real.pi * receiver.radius ^ 2)⁻¹ •
        (∫ position in receiver.domain time,
          biotSavart (family.subfamilyVorticity selected time) position) -
        biotSavart (family.subfamilyVorticity selected time) (receiver.center time) =
      receiver.radius • ((Circle.exp (receiver.phase time) : ℂ) *
        contourExteriorCentroidResponse (Circle.exp (receiver.phase time))
          (fun power => family.exteriorTaylorCoefficient selected receiver.center receiver.radius (power + 1) time)
          (receiver.shape time)) := by
  simp_rw [family.exteriorTaylorCoefficient_eq_vorticityCoefficient selected receiver.center
    receiver.radius time _ distancePositive separated]
  exact exterior_biotSavart_domain_average_eq_response (family.subfamilyVorticity_integrable selected time)
    (family.subfamilyVorticity_memLp selected time _) (family.subfamily_biotSavart_continuous selected time)
    (receiver.center time) receiver.radius_positive distancePositive
    (family.subfamily_support_separated selected (receiver.center time) time distance separated)
    smallRadius (Circle.exp (receiver.phase time)) (receiver.shape time) (receiver.nearby time) area

theorem quadrupoleExternalReceiverResidual_eq_foreign_centroid_response {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusEquation : ∀ index patch, (family.patch (finProdFinEquiv (index, patch))).radius =
      scales.radius (index.val + 1))
    (receiver : Fin count × Fin 4) (time : ℝ) {distance : ℝ}
    (distancePositive : 0 < distance)
    (separated : ∀ source ∈ foreignQuadrupolePatchLabels receiver.1,
      ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch (finProdFinEquiv receiver)).center time - position‖)
    (smallRadius : 24 * (family.patch (finProdFinEquiv receiver)).radius / distance < 1)
    (area : contourAreaFunctional ((family.patch (finProdFinEquiv receiver)).shape time) = Real.pi)
    (centered : contourCentroidFunctional ((family.patch (finProdFinEquiv receiver)).shape time) = 0) :
    quadrupoleExternalReceiverResidual scales family.patchMotion time receiver.1 receiver.2 =
      (family.patch (finProdFinEquiv receiver)).radius •
        ((Circle.exp ((family.patch (finProdFinEquiv receiver)).phase time) : ℂ) *
          contourExteriorCentroidResponse (Circle.exp ((family.patch (finProdFinEquiv receiver)).phase time))
            (fun power => family.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
              (family.patch (finProdFinEquiv receiver)).center
              (family.patch (finProdFinEquiv receiver)).radius (power + 1) time)
            ((family.patch (finProdFinEquiv receiver)).shape time)) := by
  have actual := family.subfamily_average_defect_eq_centroid_response
    (foreignQuadrupolePatchLabels receiver.1) (family.patch (finProdFinEquiv receiver)) time
    distancePositive separated smallRadius area
  unfold quadrupoleExternalReceiverResidual patchAverageVelocity
  rw [family.externalPatchVorticity_eq_subfamily scales densityEquation time receiver.1,
    family.patchCentroid_eq,
    (family.patch (finProdFinEquiv receiver)).centroid_eq_center_of_contourCentroid_zero time centered,
    ← radiusEquation receiver.1 receiver.2]
  exact actual

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
