import EulerNonuniqueness.Section8.BiotSavartInjectivity

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace EulerNonuniqueness

theorem InitialDatum.of_ae_eq_of_hasCompactSupport {first second : Vorticity}
    (datum : InitialDatum first) (equal : second =ᵐ[volume] first)
    (compact : HasCompactSupport second) : InitialDatum second := by
  refine ⟨compact, fun exponent bound =>
    (memLp_congr_ae equal).mpr (datum.2.1 exponent bound), ?_⟩
  exact (integral_congr_ae equal).trans datum.2.2

theorem InitialDatum.velocityLp_eq_of_ae_eq {first second : Vorticity}
    (firstDatum : InitialDatum first) (secondDatum : InitialDatum second)
    (equal : first =ᵐ[volume] second) : firstDatum.velocityLp = secondDatum.velocityLp := by
  have fieldsEqual := biotSavart_eq_of_ae_eq equal
  unfold InitialDatum.velocityLp
  congr 1

end EulerNonuniqueness
