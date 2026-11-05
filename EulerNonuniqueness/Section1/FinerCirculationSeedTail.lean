import EulerNonuniqueness.Section5.UniformSeedSmallness

noncomputable section

open Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.weighted_exponential_shift_total_bound (scales : Scales)
    (ratioGreaterOne : 1 < scales.ratio) (alphaPositive : 0 < scales.alpha)
    (frequencyPositive : 0 < scales.frequency) (offset : ℕ)
    (offsetBound : 1 ≤ scales.omega offset) (power : ℝ) :
    (∑' index : ℕ, scales.omega (offset + index) ^ power *
      Real.exp (-2 * scales.omega (offset + index) ^ scales.alpha)) ≤
      (scales.omega offset ^ power * Real.exp (-scales.omega offset ^ scales.alpha)) *
        ∑' index : ℕ, ({scales with frequency := 1}).omega index ^ power *
          Real.exp (-({scales with frequency := 1}).omega index ^ scales.alpha) := by
  let shifted : Scales := {scales with frequency := scales.omega offset}
  have shiftedPositive := scales.omega_pos frequencyPositive (zero_lt_one.trans ratioGreaterOne) offset
  have identity (index : ℕ) : shifted.omega index = scales.omega (offset + index) := by
    simp only [shifted, Scales.omega, pow_add]
    ring
  have fullSummable := shifted.weighted_exponential_summable shiftedPositive ratioGreaterOne
    alphaPositive power (coefficient := 2) (by norm_num)
  have unitSummable := Scales.weighted_exponential_summable {scales with frequency := 1}
    zero_lt_one ratioGreaterOne alphaPositive power (coefficient := 1) zero_lt_one
  have pointwise (index : ℕ) : shifted.omega index ^ power * Real.exp (-2 * shifted.omega index ^ scales.alpha) ≤
      (scales.omega offset ^ power * Real.exp (-scales.omega offset ^ scales.alpha)) *
        (({scales with frequency := 1}).omega index ^ power *
          Real.exp (-({scales with frequency := 1}).omega index ^ scales.alpha)) := by
    simpa only [show (2 : ℝ) / 2 = 1 by norm_num, neg_mul, one_mul] using
      (@Scales.weighted_exponential_frequency_bound scales ratioGreaterOne alphaPositive
        power 2 (scales.omega offset) (by norm_num) offsetBound index)
  have envelopeSummable : Summable (fun index : ℕ =>
      (scales.omega offset ^ power * Real.exp (-scales.omega offset ^ scales.alpha)) *
        (({scales with frequency := 1}).omega index ^ power *
          Real.exp (-({scales with frequency := 1}).omega index ^ scales.alpha))) := by
    simpa only [neg_mul, one_mul] using
      unitSummable.mul_left (scales.omega offset ^ power *
        Real.exp (-scales.omega offset ^ scales.alpha))
  have comparison := Summable.tsum_le_tsum pointwise fullSummable envelopeSummable
  simp only [tsum_mul_left] at comparison
  simpa only [identity] using comparison

theorem Scales.eventually_finer_circulation_seed_tail (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (ratioPower : 4 < scales.ratio ^ scales.alpha) (sourceOrder receiverPower : ℕ)
    {tolerance : ℝ} (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ receiver : ℕ,
      let changed : Scales := {scales with frequency := frequency}
      changed.omega (receiver + 1) ^ receiverPower *
        (∑' source : ℕ, changed.circulation (receiver + 2 + source) /
          changed.location (receiver + 2 + source) ^ sourceOrder) ≤
        tolerance * changed.seed receiver := by
  have ratioGreaterOne : 1 < scales.ratio := by linarith
  have ratioPositive : 0 < scales.ratio := by linarith
  let unit : Scales := {scales with frequency := 1}
  let envelope := ∑' index : ℕ, unit.omega index ^ ((sourceOrder + 1 : ℕ) : ℝ) *
    Real.exp (-unit.omega index ^ scales.alpha)
  let seedConstant := 2 * Real.sqrt 3 / Real.sqrt 2 * scales.ratio ^ 2
  let coefficient := 2 * Real.pi * scales.ratio ^ (sourceOrder + 1) * envelope
  have seedConstantPositive : 0 < seedConstant := by
    dsimp only [seedConstant]
    positivity
  have envelopeNonnegative : 0 ≤ envelope := by
    apply tsum_nonneg
    intro index
    exact mul_nonneg (Real.rpow_nonneg (unit.omega_pos zero_lt_one ratioPositive index).le _) (Real.exp_pos _).le
  have coefficientNonnegative : 0 ≤ coefficient := by
    dsimp only [coefficient]
    positivity
  have decay := (EulerNonuniqueness.General.tendsto_rpow_mul_exp_neg_rpow
    ((sourceOrder + 1 + receiverPower : ℕ) : ℝ) scales.alpha
    (scales.ratio ^ scales.alpha - 4) alphaPositive (by linarith)).const_mul coefficient
  simp only [mul_zero] at decay
  obtain ⟨lower, bound⟩ := (decay.eventually
    (eventually_lt_nhds (mul_pos tolerancePositive seedConstantPositive))).exists_forall_of_atTop
  filter_upwards [eventually_ge_atTop (max 1 lower)] with frequency frequencyBound receiver
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  have frequencyOne : 1 ≤ changed.frequency := (le_max_left _ _).trans frequencyBound
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have omegaLarge (index : ℕ) : changed.frequency ≤ changed.omega index := by
    exact le_mul_of_one_le_right frequencyPositive.le (one_le_pow₀ ratioGreaterOne.le)
  have omegaOne (index : ℕ) : 1 ≤ changed.omega index :=
    frequencyOne.trans (omegaLarge index)
  let nextFrequency := changed.omega (receiver + 1)
  have nextPositive : 0 < nextFrequency := changed.omega_pos frequencyPositive ratioPositive _
  have nextLarge : lower ≤ nextFrequency := (le_max_right _ _).trans
    (frequencyBound.trans (omegaLarge _))
  have nextIdentity : changed.omega (receiver + 2) = nextFrequency * scales.ratio := by
    simp only [nextFrequency, Scales.omega, changed, pow_succ]
    ring
  have summable := (changed.weighted_exponential_summable frequencyPositive ratioGreaterOne
    alphaPositive ((sourceOrder + 1 : ℕ) : ℝ) (coefficient := 2) (by norm_num)).comp_injective
      (show Function.Injective (fun source : ℕ => receiver + 2 + source) from
        fun _ _ equality => Nat.add_left_cancel equality)
  have circulationSummable : Summable (fun source : ℕ =>
      changed.circulation (receiver + 2 + source) /
        changed.location (receiver + 2 + source) ^ sourceOrder) := by
    apply Summable.of_norm_bounded _ (summable.mul_left (2 * Real.pi))
    intro source
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
      (changed.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (changed.location_pos _).le _))]
    simpa only [Real.rpow_natCast] using
      changed.circulation_div_location_pow_bound frequencyOne ratioBound sourceOrder _
  have circulationBound := Summable.tsum_le_tsum
    (fun source => by simpa only [Real.rpow_natCast] using
      changed.circulation_div_location_pow_bound frequencyOne ratioBound sourceOrder (receiver + 2 + source))
    circulationSummable (summable.mul_left (2 * Real.pi))
  rw [tsum_mul_left] at circulationBound
  have shiftedBound := changed.weighted_exponential_shift_total_bound ratioGreaterOne alphaPositive
    frequencyPositive (receiver + 2) (omegaOne _) ((sourceOrder + 1 : ℕ) : ℝ)
  have tailBound := circulationBound.trans (mul_le_mul_of_nonneg_left shiftedBound (by positivity : (0 : ℝ) ≤ 2 * Real.pi))
  have rewriteEnvelope : (∑' index : ℕ, ({changed with frequency := 1}).omega index ^ ((sourceOrder + 1 : ℕ) : ℝ) *
      Real.exp (-({changed with frequency := 1}).omega index ^ changed.alpha)) = envelope := by rfl
  rw [rewriteEnvelope, Real.rpow_natCast, nextIdentity,
    Real.mul_rpow nextPositive.le ratioPositive.le] at tailBound
  have exponentialIdentity : Real.exp (-(nextFrequency ^ scales.alpha * scales.ratio ^ scales.alpha)) =
      Real.exp (-(scales.ratio ^ scales.alpha - 4) * nextFrequency ^ scales.alpha) *
        Real.exp (-4 * nextFrequency ^ scales.alpha) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [exponentialIdentity, mul_pow] at tailBound
  have weightedTail := mul_le_mul_of_nonneg_left tailBound (pow_nonneg nextPositive.le receiverPower)
  have tailIdentity : nextFrequency ^ receiverPower *
      (2 * Real.pi * ((nextFrequency ^ (sourceOrder + 1) * scales.ratio ^ (sourceOrder + 1) *
        (Real.exp (-(scales.ratio ^ scales.alpha - 4) * nextFrequency ^ scales.alpha) *
          Real.exp (-4 * nextFrequency ^ scales.alpha))) * envelope)) =
      (coefficient * (nextFrequency ^ (sourceOrder + 1 + receiverPower) *
        Real.exp (-(scales.ratio ^ scales.alpha - 4) * nextFrequency ^ scales.alpha))) *
          Real.exp (-4 * nextFrequency ^ scales.alpha) := by
    dsimp only [coefficient]
    rw [pow_add]
    ring
  rw [tailIdentity] at weightedTail
  have pointwise := (bound nextFrequency nextLarge).le
  rw [Real.rpow_natCast] at pointwise
  have small := weightedTail.trans (mul_le_mul_of_nonneg_right pointwise (Real.exp_pos _).le)
  have locationSmall : changed.location (receiver + 1) ≤ 1 := by
    rw [changed.location_eq_inv_pow]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have inverseLarge : 1 ≤ (changed.location (receiver + 1))⁻¹ :=
    (one_le_inv₀ (changed.location_pos _)).mpr locationSmall
  have seedLower : seedConstant * Real.exp (-4 * nextFrequency ^ scales.alpha) ≤ changed.seed receiver := by
    rw [changed.seed_exact_exponential frequencyPositive ratioPositive]
    change seedConstant * Real.exp (-4 * nextFrequency ^ scales.alpha) ≤
      seedConstant * ((changed.location (receiver + 1))⁻¹ ^ 4 * Real.exp (-4 * nextFrequency ^ scales.alpha))
    exact mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ inverseLarge)) seedConstantPositive.le
  exact small.trans ((by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left seedLower tolerancePositive.le))

end EulerNonuniqueness.Paper
