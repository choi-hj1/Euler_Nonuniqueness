import EulerNonuniqueness.Section3.AffinePatchBiotSavart
import EulerNonuniqueness.Section3.FiniteContourGeometry

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

def FiniteContourConfiguration.literalDomain {count : ℕ} (configuration : FiniteContourConfiguration count)
    (data : Fin count → PeriodicC1HolderHalf)
    (small : ∀ index, ‖data index - standardCircleBanach‖ < 1 / 3) (index : Fin count) : Set ℂ :=
  affinePatchDomain (configuration.center index) (configuration.radius index) (data index) (small index)

def FiniteContourConfiguration.literalVorticity {count : ℕ} (configuration : FiniteContourConfiguration count)
    (data : Fin count → PeriodicC1HolderHalf)
    (small : ∀ index, ‖data index - standardCircleBanach‖ < 1 / 3) : Vorticity :=
  fun position => ∑ index, configuration.density index *
    (configuration.literalDomain data small index).indicator (fun _ => (1 : ℝ)) position

theorem FiniteContourConfiguration.literalDomain_isOpen {count : ℕ}
    (configuration : FiniteContourConfiguration count) (data : Fin count → PeriodicC1HolderHalf)
    (small : ∀ index, ‖data index - standardCircleBanach‖ < 1 / 3) (index : Fin count) :
    IsOpen (configuration.literalDomain data small index) :=
  affinePatchDomain_isOpen _ (configuration.radius_pos index) _ _

theorem FiniteContourConfiguration.literalDomain_isBounded {count : ℕ}
    (configuration : FiniteContourConfiguration count) (data : Fin count → PeriodicC1HolderHalf)
    (small : ∀ index, ‖data index - standardCircleBanach‖ < 1 / 3) (index : Fin count) :
    Bornology.IsBounded (configuration.literalDomain data small index) :=
  affinePatchDomain_isBounded _ (configuration.radius_pos index) _ _

theorem FiniteContourConfiguration.literalIndicator_memLp {count : ℕ}
    (configuration : FiniteContourConfiguration count) (data : Fin count → PeriodicC1HolderHalf)
    (small : ∀ index, ‖data index - standardCircleBanach‖ < 1 / 3) (index : Fin count) (exponent : ℝ≥0∞) :
    MemLp ((configuration.literalDomain data small index).indicator (fun _ => (1 : ℝ))) exponent volume :=
  memLp_indicator_const exponent (configuration.literalDomain_isOpen data small index).measurableSet 1
    (Or.inr (configuration.literalDomain_isBounded data small index).measure_lt_top.ne)

theorem FiniteContourConfiguration.literalIndicator_integrable {count : ℕ}
    (configuration : FiniteContourConfiguration count) (data : Fin count → PeriodicC1HolderHalf)
    (small : ∀ index, ‖data index - standardCircleBanach‖ < 1 / 3) (index : Fin count) :
    Integrable ((configuration.literalDomain data small index).indicator (fun _ => (1 : ℝ))) :=
  memLp_one_iff_integrable.mp (configuration.literalIndicator_memLp data small index 1)

theorem FiniteContourConfiguration.biotSavart_literalVorticity {count : ℕ}
    (configuration : FiniteContourConfiguration count) (data : Fin count → PeriodicC1HolderHalf)
    (small : ∀ index, ‖data index - standardCircleBanach‖ < 1 / 3)
    (chord_small : ∀ index, ‖data index - standardCircleBanach‖ < 2 / (3 * Real.pi)) (point : ℂ) :
    biotSavart (configuration.literalVorticity data small) point =
      ∑ index, configuration.density index • pointContourVelocity (configuration.physicalContour data index).val.1
        (configuration.physicalContour data index).val.2.val.1 point (-Real.pi) Real.pi := by
  have component_integrable (index : Fin count) :
      Integrable (fun position => configuration.density index •
        ((configuration.literalDomain data small index).indicator (fun _ => (1 : ℝ)) position •
          biotSavartKernel (point - position))) :=
    (integrable_biotSavart_integrand_of_L1_L4
      (configuration.literalIndicator_integrable data small index)
      (configuration.literalIndicator_memLp data small index _ ) point).smul _
  have integrand_identity :
      (fun position => configuration.literalVorticity data small position • biotSavartKernel (point - position)) =
      (fun position => ∑ index, configuration.density index •
        ((configuration.literalDomain data small index).indicator (fun _ => (1 : ℝ)) position •
          biotSavartKernel (point - position))) := by
    funext position
    rw [literalVorticity, Finset.sum_smul]
    simp only [mul_smul]
  unfold biotSavart
  rw [integrand_identity, integral_finset_sum _ (fun index _ => component_integrable index)]
  apply Finset.sum_congr rfl
  intro index _
  rw [integral_smul]
  have indicator_identity :
      (∫ position, (configuration.literalDomain data small index).indicator (fun _ => (1 : ℝ)) position •
        biotSavartKernel (point - position)) =
      ∫ position in configuration.literalDomain data small index, biotSavartKernel (point - position) := by
    rw [← integral_indicator (configuration.literalDomain_isOpen data small index).measurableSet]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun position => by
      by_cases inside : position ∈ configuration.literalDomain data small index <;> simp [inside]
  rw [indicator_identity]
  congr 1
  exact integral_affinePatchDomain_biotSavart_all_points (configuration.center index)
    (configuration.radius_pos index) (data index) (small index) (chord_small index) point

end

end EulerNonuniqueness.Paper
