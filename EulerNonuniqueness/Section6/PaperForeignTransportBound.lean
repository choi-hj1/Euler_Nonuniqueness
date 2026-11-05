import EulerNonuniqueness.Section6.PaperForeignWeightBound
import EulerNonuniqueness.Section6.MaterialCoefficientTransport

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000

theorem FinitePatchEvolution.foreign_material_transport_le_strain
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time radius : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (index : Fin count) (center velocity : ℂ)
    (receiverBounded : ∀ patch, motion.domain time index patch ⊆ Metric.closedBall center radius)
    (receiverSmall : 2 * radius ≤ scales.location (index.val + 1) / 24)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ patch position,
      position ∈ motion.domain time source patch →
        |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8 ≤ ‖center - position‖) :
    ‖∫ position, externalPatchVorticity scales motion time index position •
      (star (velocity - biotSavart (patchVorticity scales motion time) position) *
        (star (center - position))⁻¹ ^ 3)‖ ≤
      55296 * scales.strain * ‖velocity - biotSavart (externalPatchVorticity scales motion time index) center‖ /
        scales.location (index.val + 1) + (34504704 / Real.pi) * scales.strain ^ 2 := by
  classical
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith only [ratioBound]
  have locationPositive := scales.location_pos (index.val + 1)
  have distancePositive : 0 < scales.location (index.val + 1) / 24 := by positivity
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have sourceIntegrable := evolution.externalPatchVorticity_integrable inside index
  have receiverIntegrable := evolution.quadrupoleDensity_integrable inside index
  have sourceMembership := evolution.externalPatchVorticity_memLp inside index (ENNReal.ofReal (4 : ℝ))
  have receiverMembership := quadrupoleDensity_memLp scales motion time index
    (fun patch => (evolution.2.2.2.1 time inside index patch).1)
    (fun patch => (evolution.2.2.2.1 time inside index patch).2.1) (ENNReal.ofReal (4 : ℝ))
  have compact := evolution.externalPatchVorticity_compactSupport inside index
  obtain ⟨supportRadius, _, supportBound⟩ := compact.isCompact.isBounded.exists_pos_norm_le
  have sourceSupported : Function.support (externalPatchVorticity scales motion time index) ⊆
      Metric.closedBall 0 supportRadius := by
    intro position member
    simpa only [Metric.mem_closedBall, dist_zero_right] using supportBound position (subset_tsupport _ member)
  have sourceBounded := externalPatchVorticity_abs_le scales motion time index
  have receiverSupported : Function.support (quadrupoleDensity scales motion time index) ⊆
      Metric.closedBall center radius := by
    intro position nonzero
    by_contra outside
    have vanishing (patch : Fin 4) : patchDensity scales motion time index patch position = 0 := by
      apply indicator_of_not_mem
      exact fun member => outside (receiverBounded patch member)
    exact nonzero (by simp only [quadrupoleDensity, vanishing, Finset.sum_const_zero])
  have sourceSeparated : ∀ position ∈ Function.support (externalPatchVorticity scales motion time index),
      scales.location (index.val + 1) / 24 ≤ ‖center - position‖ := by
    apply externalPatchVorticity_support_separated
    intro source member patch position inDomain
    have different := (Finset.mem_erase.mp member).1
    have locations := scales.location_sum_le_three_distance
      (show index.val + 1 ≠ source.val + 1 from fun equal => different (Fin.ext (Nat.add_right_cancel equal).symm))
    have sourcePositive := scales.location_pos (source.val + 1)
    have lower : scales.location (index.val + 1) / 24 ≤
        |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8 := by
      linarith only [locations, sourcePositive]
    exact lower.trans (separated source member patch position inDomain)
  have actual := norm_material_coefficient_transport_le sourceIntegrable receiverIntegrable sourceMembership receiverMembership
    sourceSupported sourceBounded center velocity receiverSupported distancePositive receiverSmall sourceSeparated 0
  rw [← patchVorticity_eq_external_add_quadrupole scales motion time index] at actual
  let weight := ∫ position, inverseSquareVorticityWeight (externalPatchVorticity scales motion time index) center position
  have weightNonnegative : 0 ≤ weight := integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have weightBound : weight ≤ 2304 * scales.strain :=
    evolution.external_inverseSquare_weight_le_strain inside amplitudePositive frequencyBound ratioBound alphaPositive
      index center separated
  have massBound := evolution.quadrupoleDensity_integral_abs_le inside amplitudePositive frequencyPositive ratioPositive index
  have circulationBound : scales.circulation (index.val + 1) / scales.location (index.val + 1) ^ 2 ≤ scales.strain :=
    (div_le_iff₀ (sq_pos_of_pos locationPositive)).mpr
      (scales.circulation_le_strain_location_sq frequencyBound ratioBound alphaPositive index.val)
  have receiverCost : (∫ position, |quadrupoleDensity scales motion time index position|) / Real.pi *
      (scales.location (index.val + 1) / 24)⁻¹ ^ 2 ≤ (2304 / Real.pi) * scales.strain := by
    calc
      _ ≤ (4 * scales.circulation (index.val + 1)) / Real.pi *
          (scales.location (index.val + 1) / 24)⁻¹ ^ 2 := by gcongr
      _ = (2304 / Real.pi) * (scales.circulation (index.val + 1) / scales.location (index.val + 1) ^ 2) := by
        field_simp [locationPositive.ne']
        <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left circulationBound (by positivity)
  have firstCost := mul_le_mul_of_nonneg_left weightBound (mul_nonneg
    (norm_nonneg (velocity - biotSavart (externalPatchVorticity scales motion time index) center))
    (by positivity : 0 ≤ (scales.location (index.val + 1) / 24)⁻¹ ^ 1))
  have secondCost := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ weightNonnegative weightBound 2)
    (by positivity : 0 ≤ (((0 + 3 : ℝ) * 2 ^ (0 + 2) + 10) *
      (scales.location (index.val + 1) / 24)⁻¹ ^ 0) / (4 * Real.pi))
  have thirdCost := mul_le_mul receiverCost weightBound weightNonnegative (by positivity : 0 ≤ (2304 / Real.pi) * scales.strain)
  have scalarIdentity :
      ‖velocity - biotSavart (externalPatchVorticity scales motion time index) center‖ *
          (scales.location (index.val + 1) / 24)⁻¹ ^ 1 * (2304 * scales.strain) +
        (((0 + 3 : ℝ) * 2 ^ (0 + 2) + 10) *
          (scales.location (index.val + 1) / 24)⁻¹ ^ 0 / (4 * Real.pi)) * (2304 * scales.strain) ^ 2 +
        (2304 / Real.pi) * scales.strain * (2304 * scales.strain) =
      55296 * scales.strain * ‖velocity - biotSavart (externalPatchVorticity scales motion time index) center‖ /
        scales.location (index.val + 1) + (34504704 / Real.pi) * scales.strain ^ 2 := by
    simp only [pow_zero, pow_one]
    field_simp [locationPositive.ne']
    <;> ring
  apply actual.trans
  simpa only [weight, Nat.cast_zero, Nat.zero_add] using
    (add_le_add (add_le_add firstCost secondCost) thirdCost).trans_eq scalarIdentity

end EulerNonuniqueness.Paper
