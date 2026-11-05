import EulerNonuniqueness.Section3.RegularizedContourLogLimit
import EulerNonuniqueness.Section8.RegularizedVelocityConvergence
import Mathlib.Analysis.SpecificLimits.Basic

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace EulerNonuniqueness.Paper

noncomputable section

theorem tendsto_regularizedBiotSavart_indicator
    {scales : ℕ → ℝ} (positive : ∀ index, 0 < scales index)
    (convergence : Tendsto scales atTop (𝓝 0)) (domain : Set ℂ)
    (measurable : MeasurableSet domain) (finite : volume domain ≠ ⊤) (point : ℂ) :
    Tendsto (fun index => ∫ position in domain, regularizedBiotSavartKernel (scales index) (point - position))
      atTop (𝓝 (∫ position in domain, biotSavartKernel (point - position))) := by
  let vorticity : Vorticity := domain.indicator (fun _ => (1 : ℝ))
  have integrable : Integrable vorticity := by
    exact (memLp_one_iff_integrable).mp (memLp_indicator_const 1 measurable 1 (Or.inr finite))
  have member : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume :=
    memLp_indicator_const _ measurable 1 (Or.inr finite)
  have uniform_convergence := tendstoUniformly_regularizedBiotSavart_sub (Parameter := Unit)
    positive convergence (vorticity := fun _ _ => vorticity)
    (fun _ _ => integrable) (fun _ _ => member)
    (oneBound := ∫ position, ‖vorticity position‖)
    (fourBound := (eLpNorm vorticity (ENNReal.ofReal (4 : ℝ)) volume).toReal)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  have pointwise := (uniform_convergence.tendsto_at ((), point)).add_const (biotSavart vorticity point)
  have regularized_identity (scale : ℝ) : regularizedBiotSavart scale vorticity point =
      ∫ position in domain, regularizedBiotSavartKernel scale (point - position) := by
    unfold regularizedBiotSavart vorticity
    rw [← integral_indicator measurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun position => by
      by_cases member : position ∈ domain <;> simp [member]
  have singular_identity : biotSavart vorticity point =
      ∫ position in domain, biotSavartKernel (point - position) := by
    unfold biotSavart vorticity
    rw [← integral_indicator measurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun position => by
      by_cases member : position ∈ domain <;> simp [member]
  simpa only [sub_add_cancel, zero_add, regularized_identity, singular_identity] using pointwise

theorem integral_nearCircleInterior_regularizedBiotSavart_window
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    {scale : ℝ} (positive : 0 < scale) (point : ℂ) (windowCenter : ℝ) :
    (∫ position in nearCircleInterior data small,
      regularizedBiotSavartKernel scale (point - position)) =
      -(2 * Real.pi)⁻¹ • (∫ label in (windowCenter - Real.pi)..(windowCenter + Real.pi),
        regularizedContourLog scale point (data.val.1 label) • data.val.2.val.1 label) := by
  rw [integral_nearCircleInterior_regularizedBiotSavart data small positive point]
  have periodic : Function.Periodic
      (fun label => regularizedContourLog scale point (data.val.1 label) • data.val.2.val.1 label)
      (2 * Real.pi) := by
    intro label
    dsimp only
    rw [PeriodicC1HolderHalf.periodic data label, PeriodicHolderHalf.periodic data.val.2 label]
  congr 1
  convert periodic.intervalIntegral_add_eq (-Real.pi) (windowCenter - Real.pi) using 1 <;>
    congr 1 <;> ring

theorem integral_nearCircleInterior_biotSavart_window_of_log_integrable
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (point : ℂ) (windowCenter : ℝ)
    (nonzero : ∀ᵐ label ∂(volume.restrict (uIoc (windowCenter - Real.pi) (windowCenter + Real.pi))), data.val.1 label ≠ point)
    (log_integrable : IntervalIntegrable
      (fun label => Real.log ‖data.val.1 label - point‖ • data.val.2.val.1 label)
      volume (windowCenter - Real.pi) (windowCenter + Real.pi)) :
    (∫ position in nearCircleInterior data small, biotSavartKernel (point - position)) =
      -(2 * Real.pi)⁻¹ • (∫ label in (windowCenter - Real.pi)..(windowCenter + Real.pi),
        Real.log ‖data.val.1 label - point‖ • data.val.2.val.1 label) := by
  let scales : ℕ → ℝ := fun index => 1 / ((index : ℝ) + 1)
  have positive (index : ℕ) : 0 < scales index := by dsimp [scales]; positivity
  have scales_le (index : ℕ) : scales index ≤ 1 := by
    dsimp [scales]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) index])
  have convergence : Tendsto scales atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have radius_bound (label : ℝ) : ‖data.val.1 label - point‖ ≤ ‖data‖ + ‖point‖ + 1 := by
    exact (norm_sub_le _ _).trans (by linarith [PeriodicC1HolderHalf.value_bound data label])
  have logarithmic_limit := tendsto_intervalIntegral_regularizedContourLog positive scales_le convergence
    data.val.1 data.val.2.val.1 point (windowCenter - Real.pi) (windowCenter + Real.pi) (‖data‖ + ‖point‖ + 1)
    data.val.1.continuous data.val.2.val.1.continuous (by linarith [norm_nonneg data, norm_nonneg point])
    (fun label _ => radius_bound label) nonzero log_integrable
  have velocity_limit := tendsto_regularizedBiotSavart_indicator positive convergence
    (nearCircleInterior data small) (nearCircleInterior_isOpen data small).measurableSet
    ((nearCircleInterior_isBounded data small).measure_lt_top.ne) point
  apply tendsto_nhds_unique velocity_limit
  convert logarithmic_limit.const_smul (-(2 * Real.pi)⁻¹) using 1
  funext index
  exact integral_nearCircleInterior_regularizedBiotSavart_window data small (positive index) point windowCenter

end

end EulerNonuniqueness.Paper
