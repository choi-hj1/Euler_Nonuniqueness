import EulerNonuniqueness.Section6.MovingForeignQuadrupole
import EulerNonuniqueness.Section6.MaterialCoefficientTransport
import EulerNonuniqueness.Section6.MovingExteriorCoefficientBound
import EulerNonuniqueness.Section1.CirculationPairStrain
import EulerNonuniqueness.Section6.PaperQuadrupoleStaticMoments

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000

theorem foreign_material_transport_le_strain {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    {horizon time radius : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (index : Fin count) (center velocity : ℂ)
    (receiverBounded : ∀ patch, family.patchMotion.domain time index patch ⊆ Metric.closedBall center radius)
    (receiverSmall : 2 * radius ≤ scales.location (index.val + 1) / 24)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ patch,
      ∀ position ∈ family.patchMotion.domain time source patch,
        |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8 ≤ ‖center - position‖) :
    ‖∫ position : ℂ, externalPatchVorticity scales family.patchMotion time index position •
      (star (velocity - biotSavart (family.vorticity time) position) * (star (center - position))⁻¹ ^ 3)‖ ≤
      55296 * scales.strain * ‖velocity - biotSavart (externalPatchVorticity scales family.patchMotion time index) center‖ /
          scales.location (index.val + 1) + (34504704 / Real.pi) * scales.strain ^ 2 := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have locationPositive := scales.location_pos (index.val + 1)
  have distancePositive : 0 < scales.location (index.val + 1) / 24 := by positivity
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  let selected := foreignQuadrupolePatchLabels index
  have sourceEquation := family.externalPatchVorticity_eq_subfamily scales densityEquation time index
  have receiverEquation := family.quadrupoleDensity_eq_subfamily scales densityEquation time index
  have sourceIntegrable := family.subfamilyVorticity_integrable selected time
  have receiverIntegrable := family.subfamilyVorticity_integrable (quadrupolePatchLabels index) time
  have sourceMembership := family.subfamilyVorticity_memLp selected time (ENNReal.ofReal (4 : ℝ))
  have receiverMembership := family.subfamilyVorticity_memLp (quadrupolePatchLabels index) time (ENNReal.ofReal (4 : ℝ))
  have sourceSupported := family.subfamilyVorticity_support selected time
  have sourceBounded := family.abs_subfamilyVorticity_le selected time
  have receiverSupported : Function.support (family.subfamilyVorticity (quadrupolePatchLabels index) time) ⊆
      Metric.closedBall center radius := by
    rw [← receiverEquation]
    intro position positionNonzero
    by_contra outside
    have vanishing (patch : Fin 4) : patchDensity scales family.patchMotion time index patch position = 0 := by
      apply indicator_of_not_mem
      exact fun member => outside (receiverBounded patch member)
    exact positionNonzero (by simp only [quadrupoleDensity, vanishing, Finset.sum_const_zero])
  have labelSeparation (label : Fin (count * 4)) (member : label ∈ selected) :
      ∀ position ∈ (family.patch label).domain time,
        scales.location (index.val + 1) / 24 ≤ ‖center - position‖ := by
    obtain ⟨⟨source, patch⟩, equality⟩ := finProdFinEquiv.surjective label
    subst label
    have different := (mem_foreignQuadrupolePatchLabels index source patch).mp member
    have locations := scales.location_sum_le_three_distance
      (show index.val + 1 ≠ source.val + 1 from fun equality => different (Fin.ext (Nat.add_right_cancel equality).symm))
    have distanceLower : scales.location (index.val + 1) / 24 ≤
        |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8 := by
      linarith only [locations, (scales.location_pos (source.val + 1)).le]
    intro position positionInside
    exact distanceLower.trans (separated source (Finset.mem_erase.mpr ⟨different, Finset.mem_univ source⟩) patch position positionInside)
  have sourceSeparated := family.subfamily_support_separated selected center time
    (scales.location (index.val + 1) / 24) labelSeparation
  have actual := norm_material_coefficient_transport_le sourceIntegrable receiverIntegrable sourceMembership receiverMembership
    sourceSupported sourceBounded center velocity receiverSupported distancePositive receiverSmall sourceSeparated 0
  rw [← sourceEquation, ← receiverEquation, ← family.vorticity_eq_external_add_quadrupole scales densityEquation time index] at actual
  let weight := ∫ position, inverseSquareVorticityWeight (externalPatchVorticity scales family.patchMotion time index) center position
  have weightNonnegative : 0 ≤ weight := integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have weightBound : weight ≤ 2304 * scales.strain :=
    family.external_inverseSquare_weight_le_strain scales evolution inside densityEquation amplitudePositive frequencyBound
      ratioBound alphaPositive index center separated
  have massBound := evolution.quadrupoleDensity_integral_abs_le inside amplitudePositive frequencyPositive ratioPositive index
  have circulationBound : scales.circulation (index.val + 1) / scales.location (index.val + 1) ^ 2 ≤ scales.strain :=
    (div_le_iff₀ (sq_pos_of_pos locationPositive)).mpr
      (scales.circulation_le_strain_location_sq frequencyBound ratioBound alphaPositive index.val)
  have receiverCost : (∫ position, |quadrupoleDensity scales family.patchMotion time index position|) / Real.pi *
      (scales.location (index.val + 1) / 24)⁻¹ ^ 2 ≤ (2304 / Real.pi) * scales.strain := by
    calc
      _ ≤ (4 * scales.circulation (index.val + 1)) / Real.pi *
          (scales.location (index.val + 1) / 24)⁻¹ ^ 2 := by gcongr
      _ = (2304 / Real.pi) * (scales.circulation (index.val + 1) / scales.location (index.val + 1) ^ 2) := by
        field_simp [locationPositive.ne']
        <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left circulationBound (by positivity)
  have firstCost := mul_le_mul_of_nonneg_left weightBound (mul_nonneg
    (norm_nonneg (velocity - biotSavart (externalPatchVorticity scales family.patchMotion time index) center))
    (by positivity : 0 ≤ (scales.location (index.val + 1) / 24)⁻¹ ^ 1))
  have secondCost := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ weightNonnegative weightBound 2)
    (by positivity : 0 ≤ (((0 + 3 : ℝ) * 2 ^ (0 + 2) + 10) *
      (scales.location (index.val + 1) / 24)⁻¹ ^ 0) / (4 * Real.pi))
  have thirdCost := mul_le_mul receiverCost weightBound weightNonnegative (by positivity : 0 ≤ (2304 / Real.pi) * scales.strain)
  have scalarIdentity :
      ‖velocity - biotSavart (externalPatchVorticity scales family.patchMotion time index) center‖ *
          (scales.location (index.val + 1) / 24)⁻¹ ^ 1 * (2304 * scales.strain) +
        (((0 + 3 : ℝ) * 2 ^ (0 + 2) + 10) *
          (scales.location (index.val + 1) / 24)⁻¹ ^ 0 / (4 * Real.pi)) * (2304 * scales.strain) ^ 2 +
        (2304 / Real.pi) * scales.strain * (2304 * scales.strain) =
      55296 * scales.strain * ‖velocity - biotSavart (externalPatchVorticity scales family.patchMotion time index) center‖ /
        scales.location (index.val + 1) + (34504704 / Real.pi) * scales.strain ^ 2 := by
    simp only [pow_zero, pow_one]
    field_simp [locationPositive.ne']
    <;> ring
  apply actual.trans
  simpa only [weight, Nat.cast_zero, Nat.zero_add] using
    (add_le_add (add_le_add firstCost secondCost) thirdCost).trans_eq scalarIdentity

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
