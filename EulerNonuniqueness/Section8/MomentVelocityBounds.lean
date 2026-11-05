import EulerNonuniqueness.Section8.MomentCompactnessData

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem MomentCompactnessData.uniform_biotSavart_decay
    {horizon : ℝ} {sequence : ℕ → Evolution} (data : MomentCompactnessData horizon sequence) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ index, ∀ time ∈ Icc 0 horizon, ∀ position,
      ‖biotSavart (sequence index time) position‖ ≤ bound * (1 + ‖position‖ ^ 2)⁻¹ := by
  obtain ⟨radius, radiusPositive, supported⟩ := data.supported
  let cutoff := max (2 * radius) 1
  obtain ⟨velocityBound, velocityNonnegative, velocityBounded⟩ := data.uniform_velocity_bound
  obtain ⟨massBound, massBoundFinite, massBounded⟩ := data.normBounded 1 le_rfl
  let farCoefficient := massBound.toReal * radius / Real.pi
  have coefficientNonnegative : 0 ≤ farCoefficient := by dsimp [farCoefficient]; positivity
  let bound := velocityBound * (1 + cutoff ^ 2) + 2 * farCoefficient
  refine ⟨bound, by dsimp [bound]; positivity, ?_⟩
  intro index time inside position
  apply (le_div_iff₀ (by positivity : 0 < 1 + ‖position‖ ^ 2)).mpr
  change ‖biotSavart (sequence index time) position‖ * (1 + ‖position‖ ^ 2) ≤ bound
  by_cases nearby : ‖position‖ ≤ cutoff
  · have squareBound : ‖position‖ ^ 2 ≤ cutoff ^ 2 := pow_le_pow_left₀ (norm_nonneg _) nearby 2
    calc
      _ ≤ velocityBound * (1 + ‖position‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (velocityBounded index time inside position) (by positivity)
      _ ≤ velocityBound * (1 + cutoff ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add_left squareBound _) velocityNonnegative
      _ ≤ bound := le_add_of_nonneg_right (by positivity)
  · have far : cutoff ≤ ‖position‖ := (lt_of_not_ge nearby).le
    have positionOne : 1 ≤ ‖position‖ := (le_max_right _ _).trans far
    have positionPositive : 0 < ‖position‖ := zero_lt_one.trans_le positionOne
    have integrable : Integrable (sequence index time) := memLp_one_iff_integrable.mp
      (by simpa only [ENNReal.ofReal_one] using data.members 1 le_rfl index time inside)
    have massEstimate : (∫ source, |sequence index time source|) ≤ massBound.toReal := by
      have estimate := ENNReal.toReal_mono massBoundFinite.ne (massBounded index time inside)
      simpa only [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm,
        ← integral_norm_eq_lintegral_enorm integrable.aestronglyMeasurable, Real.norm_eq_abs] using estimate
    have velocityEstimate := norm_biotSavart_le_of_support_integral_zero integrable
      (data.zeroMean index time inside) (supported index time inside) positionPositive ((le_max_left _ _).trans far)
    have normEstimate : ‖biotSavart (sequence index time) position‖ ≤ farCoefficient / ‖position‖ ^ 2 := by
      apply velocityEstimate.trans
      calc
        _ ≤ massBound.toReal * radius / (Real.pi * ‖position‖ ^ 2) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right massEstimate radiusPositive.le) (by positivity)
        _ = _ := by dsimp [farCoefficient]; ring
    have squareLower : 1 ≤ ‖position‖ ^ 2 := by nlinarith [norm_nonneg position]
    have rationalEstimate : farCoefficient / ‖position‖ ^ 2 * (1 + ‖position‖ ^ 2) ≤ 2 * farCoefficient := by
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ (sq_pos_of_pos positionPositive)).mpr (by nlinarith)
    calc
      _ ≤ farCoefficient / ‖position‖ ^ 2 * (1 + ‖position‖ ^ 2) :=
        mul_le_mul_of_nonneg_right normEstimate (by positivity)
      _ ≤ 2 * farCoefficient := rationalEstimate
      _ ≤ bound := le_add_of_nonneg_left (by positivity)

theorem MomentCompactnessData.biotSavart_L2_dominator
    {horizon : ℝ} {sequence : ℕ → Evolution} (data : MomentCompactnessData horizon sequence) :
    ∃ bound : Plane → ℝ, MemLp bound 2 volume ∧
      ∀ index, ∀ time ∈ Icc 0 horizon, ∀ position,
        ‖biotSavart (sequence index time) position‖ ≤ ‖bound position‖ := by
  obtain ⟨coefficient, coefficientNonnegative, bounded⟩ := data.uniform_biotSavart_decay
  refine ⟨fun position => coefficient * (1 + ‖position‖ ^ 2)⁻¹,
    memLp_inverse_one_add_norm_sq.const_mul coefficient, ?_⟩
  intro index time inside position
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact bounded index time inside position

end EulerNonuniqueness
