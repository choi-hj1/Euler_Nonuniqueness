import EulerNonuniqueness.Section6.CoMovingTransportBound
import EulerNonuniqueness.Section6.ReceiverTransportCoefficientBound

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Section6

theorem biotSavart_add_of_L1_L4 {first second : Vorticity}
    (firstIntegrable : Integrable first) (secondIntegrable : Integrable second)
    (firstMembership : MemLp first (ENNReal.ofReal (4 : ℝ)) volume)
    (secondMembership : MemLp second (ENNReal.ofReal (4 : ℝ)) volume) (position : ℂ) :
    biotSavart (first + second) position = biotSavart first position + biotSavart second position := by
  have firstAt := integrable_biotSavart_integrand_of_L1_L4 firstIntegrable firstMembership position
  have secondAt := integrable_biotSavart_integrand_of_L1_L4 secondIntegrable secondMembership position
  unfold biotSavart
  simp only [Pi.add_apply, add_smul]
  exact integral_add firstAt secondAt

theorem material_coefficient_transport_decomposition {source receiver : Vorticity}
    (sourceIntegrable : Integrable source) (receiverIntegrable : Integrable receiver)
    (sourceMembership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    (receiverMembership : MemLp receiver (ENNReal.ofReal (4 : ℝ)) volume)
    {supportRadius bound radius distance : ℝ}
    (sourceSupported : Function.support source ⊆ Metric.closedBall 0 supportRadius)
    (sourceBounded : ∀ position, |source position| ≤ bound)
    (center velocity : ℂ)
    (receiverSupported : Function.support receiver ⊆ Metric.closedBall center radius)
    (positive : 0 < distance) (small : 2 * radius ≤ distance)
    (separated : ∀ position ∈ Function.support source, distance ≤ ‖center - position‖)
    (power : ℕ) :
    (∫ position : ℂ, source position • (star (velocity - biotSavart (source + receiver) position) *
      (star (center - position))⁻¹ ^ (power + 3))) =
      star (velocity - biotSavart source center) *
        (∫ position : ℂ, source position • (star (center - position))⁻¹ ^ (power + 3)) +
      (∫ position : ℂ, source position • (star (biotSavart source center - biotSavart source position) *
        (star (center - position))⁻¹ ^ (power + 3))) -
      ∫ position : ℂ, source position • (star (biotSavart receiver position) *
        (star (center - position))⁻¹ ^ (power + 3)) := by
  have inverseIntegrable := integrable_exterior_inverse_power sourceIntegrable center positive separated (power + 1)
  have constantIntegrable : Integrable (fun position : ℂ =>
      star (velocity - biotSavart source center) *
        (source position • (star (center - position))⁻¹ ^ (power + 3))) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      inverseIntegrable.const_mul (star (velocity - biotSavart source center))
  have coMovingIntegrable := integrable_coMoving_transport sourceIntegrable sourceMembership
    sourceSupported sourceBounded center positive separated (power + 3)
  have receiverTermIntegrable := integrable_receiver_transport_coefficient sourceIntegrable receiverIntegrable
    center receiverSupported positive small separated power
  have sumIntegrable : Integrable (fun position : ℂ =>
      star (velocity - biotSavart source center) * (source position • (star (center - position))⁻¹ ^ (power + 3)) +
      source position • (star (biotSavart source center - biotSavart source position) *
        (star (center - position))⁻¹ ^ (power + 3))) := constantIntegrable.add coMovingIntegrable
  rw [← integral_const_mul, ← integral_add constantIntegrable coMovingIntegrable,
    ← integral_sub sumIntegrable receiverTermIntegrable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun position => by
    dsimp only
    rw [biotSavart_add_of_L1_L4 sourceIntegrable receiverIntegrable sourceMembership receiverMembership]
    simp only [Complex.star_def, map_sub, map_add, Complex.real_smul]
    ring

theorem norm_material_coefficient_transport_le {source receiver : Vorticity}
    (sourceIntegrable : Integrable source) (receiverIntegrable : Integrable receiver)
    (sourceMembership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    (receiverMembership : MemLp receiver (ENNReal.ofReal (4 : ℝ)) volume)
    {supportRadius bound radius distance : ℝ}
    (sourceSupported : Function.support source ⊆ Metric.closedBall 0 supportRadius)
    (sourceBounded : ∀ position, |source position| ≤ bound)
    (center velocity : ℂ)
    (receiverSupported : Function.support receiver ⊆ Metric.closedBall center radius)
    (positive : 0 < distance) (small : 2 * radius ≤ distance)
    (separated : ∀ position ∈ Function.support source, distance ≤ ‖center - position‖)
    (power : ℕ) :
    ‖∫ position : ℂ, source position • (star (velocity - biotSavart (source + receiver) position) *
      (star (center - position))⁻¹ ^ (power + 3))‖ ≤
      ‖velocity - biotSavart source center‖ * distance⁻¹ ^ (power + 1) *
        (∫ position, inverseSquareVorticityWeight source center position) +
      ((((power + 3 : ℝ) * 2 ^ (power + 2) + 10) * distance⁻¹ ^ power) / (4 * Real.pi)) *
        (∫ position, inverseSquareVorticityWeight source center position) ^ 2 +
      ((∫ location, |receiver location|) / Real.pi * distance⁻¹ ^ (power + 2)) *
        (∫ position, inverseSquareVorticityWeight source center position) := by
  rw [material_coefficient_transport_decomposition sourceIntegrable receiverIntegrable sourceMembership
    receiverMembership sourceSupported sourceBounded center velocity receiverSupported positive small separated power]
  have constantBound := norm_integral_exterior_inverse_power sourceIntegrable center positive separated (power + 1)
  have coMovingBound := norm_coMoving_transport_integral_bound sourceIntegrable sourceMembership
    sourceSupported sourceBounded center positive separated power
  have receiverBound := norm_integral_receiver_transport_coefficient_le sourceIntegrable receiverIntegrable
    center receiverSupported positive small separated power
  apply (norm_sub_le _ _).trans
  apply add_le_add _ receiverBound
  apply (norm_add_le _ _).trans
  apply add_le_add _ coMovingBound
  rw [norm_mul, norm_star]
  have scaled := mul_le_mul_of_nonneg_left constantBound (norm_nonneg (velocity - biotSavart source center))
  simpa only [Nat.add_assoc, Nat.reduceAdd, mul_assoc] using scaled

end EulerNonuniqueness.Section6
