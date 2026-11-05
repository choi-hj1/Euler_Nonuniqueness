import EulerNonuniqueness.Section8.Curl
import EulerNonuniqueness.Section8.InitialVelocity

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem biotSavart_eq_of_ae_eq {first second : Vorticity} (equal : first =ᵐ[volume] second) :
    biotSavart first = biotSavart second := by
  funext position
  apply integral_congr_ae
  filter_upwards [equal] with source equality
  rw [equality]

def InitialDatum.velocityLp {initial : Vorticity} (datum : InitialDatum initial) :
    Lp Plane 2 (volume : Measure Plane) :=
  datum.biotSavart_memLp_two.toLp (biotSavart initial)

theorem InitialDatum.ae_eq_of_biotSavart_ae_eq {first second : Vorticity}
    (firstDatum : InitialDatum first) (secondDatum : InitialDatum second)
    (equal : biotSavart first =ᵐ[volume] biotSavart second) : first =ᵐ[volume] second := by
  have firstIntegrable : Integrable first := memLp_one_iff_integrable.mp
    (by simpa using firstDatum.2.1 1 le_rfl)
  have secondIntegrable : Integrable second := memLp_one_iff_integrable.mp
    (by simpa using secondDatum.2.1 1 le_rfl)
  obtain ⟨firstRadius, firstPositive, firstSupported⟩ := firstDatum.exists_support_radius
  obtain ⟨secondRadius, secondPositive, secondSupported⟩ := secondDatum.exists_support_radius
  apply ae_eq_of_integral_contDiff_smul_eq firstIntegrable.locallyIntegrable secondIntegrable.locallyIntegrable
  intro test smooth compact
  have firstCurl := (curl_biotSavart_of_integrable_support firstIntegrable firstSupported smooth compact).2
  have secondCurl := (curl_biotSavart_of_integrable_support secondIntegrable secondSupported smooth compact).2
  have curlEquality :
      (∫ position, fderiv ℝ test position (Complex.I * biotSavart first position)) =
        ∫ position, fderiv ℝ test position (Complex.I * biotSavart second position) := by
    apply integral_congr_ae
    filter_upwards [equal] with position equality
    rw [equality]
  have momentEquality := firstCurl.symm.trans (curlEquality.trans secondCurl)
  simpa only [smul_eq_mul, mul_comm] using momentEquality

theorem InitialDatum.ae_eq_of_velocityLp_eq {first second : Vorticity}
    (firstDatum : InitialDatum first) (secondDatum : InitialDatum second)
    (equal : firstDatum.velocityLp = secondDatum.velocityLp) : first =ᵐ[volume] second := by
  apply firstDatum.ae_eq_of_biotSavart_ae_eq secondDatum
  have equality := congrArg (fun field : Lp Plane 2 (volume : Measure Plane) => (field : Plane → Plane)) equal
  filter_upwards [firstDatum.biotSavart_memLp_two.coeFn_toLp,
    secondDatum.biotSavart_memLp_two.coeFn_toLp] with position firstEquality secondEquality
  exact firstEquality.symm.trans ((congrFun equality position).trans secondEquality)

end EulerNonuniqueness
