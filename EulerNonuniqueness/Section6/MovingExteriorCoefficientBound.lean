import EulerNonuniqueness.Section6.ExteriorCoefficientBound
import EulerNonuniqueness.Section6.MovingExteriorTaylorCoefficient
import EulerNonuniqueness.Section6.MovingPatchSubfamily

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem exteriorTaylorCoefficient_eq_vorticityCoefficient {count : ℕ}
    (family : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (center : ℝ → ℂ) (radius time : ℝ) (power : ℕ) {distance : ℝ}
    (positive : 0 < distance)
    (separated : ∀ source ∈ selected, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖center time - position‖) :
    family.exteriorTaylorCoefficient selected center radius (power + 1) time =
      exteriorVorticityCoefficient (family.subfamilyVorticity selected time) (center time) radius power := by
  have sourceIntegrable (source : Fin count) (member : source ∈ selected) :
      IntegrableOn (fun position : ℂ => (star (center time - position))⁻¹ ^ (power + 2))
        ((family.patch source).domain time) := by
    have smooth : IntegrableOn (fun position : ℂ => smoothConjugateInversePower distance (power + 2)
        (center time - position)) ((family.patch source).domain time) := (family.patch source).integral_continuous_function time
      ((smoothConjugateInversePower_contDiff positive (power + 2)).continuous.comp
        (continuous_const.sub continuous_id))
    apply smooth.congr_fun _ ((family.patch source).domain_isOpen time).measurableSet
    intro position inside
    exact (smoothConjugateInversePower_eventuallyEq positive (power + 2)
      (separated source member position inside)).self_of_nhds
  unfold exteriorTaylorCoefficient exteriorVorticityCoefficient
  simp only [Nat.add_sub_cancel, Nat.add_assoc, Nat.reduceAdd]
  rw [family.integral_subfamilyVorticity_smul selected time _ sourceIntegrable]

theorem subfamily_support_separated {count : ℕ}
    (family : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (center : ℂ) (time distance : ℝ)
    (separated : ∀ source ∈ selected, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖center - position‖) :
    ∀ position ∈ Function.support (family.subfamilyVorticity selected time), distance ≤ ‖center - position‖ := by
  intro position nonzero
  by_contra outside
  apply nonzero
  have vanishing : ∀ source ∈ selected, family.patchVorticity time source position = 0 := by
    intro source member
    apply indicator_of_not_mem
    intro inside
    exact outside (separated source member position inside)
  exact Finset.sum_eq_zero fun source member => vanishing source member

theorem summable_weighted_exteriorTaylorCoefficient {count : ℕ}
    (family : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (center : ℝ → ℂ) (radius time : ℝ) {distance : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (separated : ∀ source ∈ selected, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖center time - position‖) (small : 2 * radius / distance < 1) :
    Summable (fun power : ℕ => (2 : ℝ) ^ (power + 1) *
      ‖family.exteriorTaylorCoefficient selected center radius (power + 1) time‖) := by
  simp_rw [family.exteriorTaylorCoefficient_eq_vorticityCoefficient selected center radius time _ positive separated]
  exact summable_weighted_exteriorVorticityCoefficient
    (family.subfamilyVorticity_integrable selected time) (center time) radiusNonnegative positive
    (family.subfamily_support_separated selected (center time) time distance separated) small

theorem tsum_weighted_exteriorTaylorCoefficient_le {count : ℕ}
    (family : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (center : ℝ → ℂ) (radius time : ℝ) {distance : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (separated : ∀ source ∈ selected, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖center time - position‖) (small : 2 * radius / distance < 1) :
    (∑' power : ℕ, (2 : ℝ) ^ (power + 1) *
      ‖family.exteriorTaylorCoefficient selected center radius (power + 1) time‖) ≤
      (1 - 2 * radius / distance)⁻¹ * (2 *
        ((∫ position, inverseSquareVorticityWeight (family.subfamilyVorticity selected time)
          (center time) position) / (2 * Real.pi))) := by
  simp_rw [family.exteriorTaylorCoefficient_eq_vorticityCoefficient selected center radius time _ positive separated]
  exact tsum_weighted_exteriorVorticityCoefficient_le
    (family.subfamilyVorticity_integrable selected time) (center time) radiusNonnegative positive
    (family.subfamily_support_separated selected (center time) time distance separated) small

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
