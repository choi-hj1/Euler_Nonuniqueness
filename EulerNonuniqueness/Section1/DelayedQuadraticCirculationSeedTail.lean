import EulerNonuniqueness.Section1.FinerCirculationSeedTail
import EulerNonuniqueness.Section1.UniformScaleBounds

noncomputable section

open Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_delayed_quadratic_circulation_seed_tail (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (alphaSmall : scales.alpha < 1) (ratioPower : 4 < scales.ratio ^ scales.alpha)
    {growth ageConstant : ℝ} (growthNonnegative : 0 ≤ growth)
    (ageConstantNonnegative : 0 ≤ ageConstant)
    (ratioSeparation : (growth + 1) * ageConstant ≤
      scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1))
    (power : ℕ) {tolerance : ℝ} (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ receiver : ℕ, ∀ selected : Finset ℕ,
      (∀ source ∈ selected, receiver + 2 ≤ source) → ∀ age : ℕ → ℝ,
      let changed : Scales := {scales with frequency := frequency}
      (∀ source ∈ selected, 0 ≤ age source ∧
        changed.omega receiver * age source ≤
          ageConstant * changed.omega (receiver + 1) ^ changed.alpha /
            (changed.ratio ^ (1 - changed.alpha) - 1)) →
      changed.omega receiver ^ power /
          (changed.omega receiver ^ 2 * changed.location receiver ^ 4) *
        (∑ source ∈ selected, (1 + (changed.location source)⁻¹) *
          changed.circulation source ^ 2 * (1 + changed.omega receiver * age source) *
          Real.exp (growth * changed.omega receiver * age source)) ≤
        tolerance * changed.seed receiver / changed.ratio ^ 2 := by
  classical
  have ratioGreaterOne : 1 < scales.ratio := by linarith only [ratioBound]
  have ratioPositive : 0 < scales.ratio := zero_lt_one.trans ratioGreaterOne
  have denominatorPositive : 0 < scales.ratio ^ (1 - scales.alpha) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow ratioGreaterOne (sub_pos.mpr alphaSmall))
  have totalDecay := (scales.weighted_exponential_total_tendsto_zero ratioGreaterOne
    alphaPositive 1 (coefficient := 1) zero_lt_one).const_mul (2 * Real.pi)
  simp only [mul_zero] at totalDecay
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    totalDecay.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    scales.eventually_finer_circulation_seed_tail ratioBound alphaPositive ratioPower 1 (power + 2)
      (tolerancePositive := div_pos tolerancePositive (by positivity : (0 : ℝ) < 2 * scales.ratio ^ 2))]
    with frequency frequencyOne totalSmall tailSmall
  intro receiver selected older age
  dsimp only
  intro ageBounds
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have omegaPositive (index : ℕ) : 0 < changed.omega index :=
    changed.omega_pos frequencyPositive ratioPositive index
  have omegaMonotone {first second : ℕ} (ordered : first ≤ second) :
      changed.omega first ≤ changed.omega second :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ratioGreaterOne.le ordered) frequencyPositive.le
  have inverseLocation (index : ℕ) : (changed.location index)⁻¹ ≤ changed.omega index := by
    rw [changed.location_eq_inv_pow, inv_inv]
    exact (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ratioBound index).trans
      (le_mul_of_one_le_left (pow_nonneg ratioPositive.le index) frequencyOne)
  have gammaNonnegative (index : ℕ) : 0 ≤ changed.circulation index :=
    (changed.circulation_pos frequencyPositive ratioPositive index).le
  have weightedSummable := changed.weighted_exponential_summable frequencyPositive
    ratioGreaterOne alphaPositive 1 (coefficient := 1) zero_lt_one
  have exponentialSmall (index : ℕ) :
      2 * Real.pi * changed.omega index * Real.exp (-changed.omega index ^ changed.alpha) ≤ 1 := by
    have bound := weightedSummable.le_tsum index (fun other _ =>
      mul_nonneg (Real.rpow_nonneg (omegaPositive other).le _) (Real.exp_pos _).le)
    have scaled := mul_le_mul_of_nonneg_left bound (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    have small : 2 * Real.pi * (∑' other : ℕ, changed.omega other ^ (1 : ℝ) *
        Real.exp (-(1 : ℝ) * changed.omega other ^ changed.alpha)) < 1 := totalSmall
    have pointwise : 2 * Real.pi * changed.omega index * Real.exp (-changed.omega index ^ changed.alpha) ≤
        2 * Real.pi * (∑' other : ℕ, changed.omega other ^ (1 : ℝ) *
          Real.exp (-(1 : ℝ) * changed.omega other ^ changed.alpha)) := by
      simpa only [Real.rpow_one, neg_one_mul, mul_assoc] using scaled
    exact pointwise.trans small.le
  have strengthBound (source : ℕ) (member : source ∈ selected) :
      changed.circulation source ^ 2 * (1 + changed.omega receiver * age source) *
        Real.exp (growth * changed.omega receiver * age source) ≤ changed.circulation source := by
    let elapsed := changed.omega receiver * age source
    have elapsedNonnegative : 0 ≤ elapsed := mul_nonneg (omegaPositive receiver).le (ageBounds source member).1
    have nextIdentity : changed.omega (receiver + 2) ^ changed.alpha =
        changed.omega (receiver + 1) ^ changed.alpha * changed.ratio ^ changed.alpha := by
      have recurrence : changed.omega (receiver + 2) = changed.omega (receiver + 1) * changed.ratio := by
        simp only [Scales.omega, pow_succ]
        ring
      rw [recurrence, Real.mul_rpow (omegaPositive _).le ratioPositive.le]
    have exponentBound : (growth + 1) * elapsed ≤ changed.omega source ^ changed.alpha := by
      have first := mul_le_mul_of_nonneg_left (ageBounds source member).2
        (show 0 ≤ growth + 1 by linarith only [growthNonnegative])
      have coefficient : (growth + 1) * ageConstant /
          (changed.ratio ^ (1 - changed.alpha) - 1) ≤ changed.ratio ^ changed.alpha :=
        (div_le_iff₀ denominatorPositive).mpr ratioSeparation
      have second := mul_le_mul
        (le_refl (changed.omega (receiver + 1) ^ changed.alpha)) coefficient
        (div_nonneg (mul_nonneg (by linarith only [growthNonnegative]) ageConstantNonnegative)
          denominatorPositive.le)
        (Real.rpow_nonneg (omegaPositive (receiver + 1)).le changed.alpha)
      have sourceLarger := Real.rpow_le_rpow (omegaPositive (receiver + 2)).le
        (omegaMonotone (older source member)) alphaPositive.le
      calc
        (growth + 1) * elapsed ≤
            (growth + 1) * (ageConstant * changed.omega (receiver + 1) ^ changed.alpha /
              (changed.ratio ^ (1 - changed.alpha) - 1)) := first
        _ = ((growth + 1) * ageConstant / (changed.ratio ^ (1 - changed.alpha) - 1)) *
            changed.omega (receiver + 1) ^ changed.alpha := by ring
        _ ≤ changed.ratio ^ changed.alpha * changed.omega (receiver + 1) ^ changed.alpha := by
          simpa only [mul_comm] using second
        _ = changed.omega (receiver + 2) ^ changed.alpha := by rw [nextIdentity]; ring
        _ ≤ changed.omega source ^ changed.alpha := sourceLarger
    have polynomial : 1 + elapsed ≤ Real.exp elapsed := by
      nlinarith only [Real.add_one_le_exp elapsed, elapsedNonnegative]
    have ageExponential : (1 + elapsed) * Real.exp (growth * elapsed) ≤
        Real.exp (changed.omega source ^ changed.alpha) := by
      calc
        _ ≤ Real.exp elapsed * Real.exp (growth * elapsed) :=
          mul_le_mul_of_nonneg_right polynomial (Real.exp_pos _).le
        _ = Real.exp ((growth + 1) * elapsed) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ _ := Real.exp_le_exp.mpr exponentBound
    have gammaSmall : changed.circulation source * Real.exp (changed.omega source ^ changed.alpha) ≤ 1 := by
      rw [Scales.circulation, changed.length_sq]
      have identity : Real.exp (-2 * changed.omega source ^ changed.alpha) *
          Real.exp (changed.omega source ^ changed.alpha) = Real.exp (-changed.omega source ^ changed.alpha) := by
        rw [← Real.exp_add]
        congr 1
        ring
      simpa only [mul_assoc, identity] using exponentialSmall source
    calc
      _ = changed.circulation source ^ 2 * ((1 + elapsed) * Real.exp (growth * elapsed)) := by
        dsimp only [elapsed]
        simp only [mul_assoc]
      _ ≤ changed.circulation source ^ 2 * Real.exp (changed.omega source ^ changed.alpha) :=
        mul_le_mul_of_nonneg_left ageExponential (sq_nonneg _)
      _ = changed.circulation source *
          (changed.circulation source * Real.exp (changed.omega source ^ changed.alpha)) := by ring
      _ ≤ changed.circulation source * 1 := mul_le_mul_of_nonneg_left gammaSmall (gammaNonnegative source)
      _ = _ := mul_one _
  have finiteComparison :
      (∑ source ∈ selected, (1 + (changed.location source)⁻¹) *
        changed.circulation source ^ 2 * (1 + changed.omega receiver * age source) *
        Real.exp (growth * changed.omega receiver * age source)) ≤
      2 * ∑ source ∈ selected, changed.circulation source / changed.location source := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro source member
    have inverseOne : 1 ≤ (changed.location source)⁻¹ :=
      (one_le_inv₀ (changed.location_pos source)).mpr (changed.location_le_one source)
    have first := mul_le_mul_of_nonneg_left (strengthBound source member)
      (show 0 ≤ 1 + (changed.location source)⁻¹ by positivity)
    have second := mul_le_mul_of_nonneg_right (show 1 + (changed.location source)⁻¹ ≤
      2 * (changed.location source)⁻¹ by linarith only [inverseOne]) (gammaNonnegative source)
    have firstBound : (1 + (changed.location source)⁻¹) * changed.circulation source ^ 2 *
        (1 + changed.omega receiver * age source) * Real.exp (growth * changed.omega receiver * age source) ≤
        (1 + (changed.location source)⁻¹) * changed.circulation source := by
      simpa only [mul_assoc] using first
    exact firstBound.trans (by simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using second)
  have shiftedSummable : Summable (fun offset : ℕ =>
      changed.circulation (receiver + 2 + offset) / changed.location (receiver + 2 + offset)) := by
    have full := changed.circulation_location_summable frequencyOne ratioBound alphaPositive 1
    have shifted := full.comp_injective
      (show Function.Injective (fun offset : ℕ => receiver + 1 + offset) from fun _ _ equal => Nat.add_left_cancel equal)
    simpa only [pow_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using shifted
  have finiteTail : (∑ source ∈ selected, changed.circulation source / changed.location source) ≤
      ∑' offset : ℕ, changed.circulation (receiver + 2 + offset) / changed.location (receiver + 2 + offset) := by
    have reindex : (∑ offset ∈ selected.image (fun source => source - (receiver + 2)),
        changed.circulation (receiver + 2 + offset) / changed.location (receiver + 2 + offset)) =
        ∑ source ∈ selected, changed.circulation source / changed.location source := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro source member
        rw [Nat.add_sub_of_le (older source member)]
      · intro first firstMember second secondMember equal
        have firstBound := older first firstMember
        have secondBound := older second secondMember
        omega
    rw [← reindex]
    exact shiftedSummable.sum_le_tsum _ (fun offset _ =>
      div_nonneg (gammaNonnegative _) (changed.location_pos _).le)
  have prefactorBound : changed.omega receiver ^ power /
      (changed.omega receiver ^ 2 * changed.location receiver ^ 4) ≤
      changed.omega (receiver + 1) ^ (power + 2) := by
    have locationPower := pow_le_pow_left₀ (inv_nonneg.mpr (changed.location_pos receiver).le)
      (inverseLocation receiver) 4
    have normalized : changed.omega receiver ^ power /
        (changed.omega receiver ^ 2 * changed.location receiver ^ 4) ≤ changed.omega receiver ^ (power + 2) := by
      calc
        _ = (changed.omega receiver ^ power / changed.omega receiver ^ 2) *
            (changed.location receiver)⁻¹ ^ 4 := by rw [inv_pow]; ring
        _ ≤ (changed.omega receiver ^ power / changed.omega receiver ^ 2) * changed.omega receiver ^ 4 :=
          mul_le_mul_of_nonneg_left locationPower
            (div_nonneg (pow_nonneg (omegaPositive receiver).le _) (sq_nonneg _))
        _ = changed.omega receiver ^ (power + 2) := by
          rw [pow_add]
          field_simp [(omegaPositive receiver).ne']
          ring
    exact normalized.trans (pow_le_pow_left₀ (omegaPositive receiver).le (omegaMonotone (Nat.le_succ receiver)) _)
  have prefactorNonnegative : 0 ≤ changed.omega receiver ^ power /
      (changed.omega receiver ^ 2 * changed.location receiver ^ 4) := by
    exact div_nonneg (pow_nonneg (omegaPositive receiver).le _)
      (mul_nonneg (sq_nonneg _) (pow_nonneg (changed.location_pos receiver).le _))
  have sumNonnegative : 0 ≤ 2 * ∑ source ∈ selected, changed.circulation source / changed.location source :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg (fun source _ =>
      div_nonneg (gammaNonnegative source) (changed.location_pos source).le))
  have combined := mul_le_mul finiteComparison prefactorBound prefactorNonnegative sumNonnegative
  have tail := tailSmall receiver
  simp only [pow_one] at tail
  have finalBound := mul_le_mul_of_nonneg_left tail (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ 2 * (changed.omega (receiver + 1) ^ (power + 2) *
        (∑ source ∈ selected, changed.circulation source / changed.location source)) := by
      convert combined using 1 <;> ring
    _ ≤ 2 * (changed.omega (receiver + 1) ^ (power + 2) *
        (∑' offset : ℕ, changed.circulation (receiver + 2 + offset) / changed.location (receiver + 2 + offset))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left finiteTail
        (pow_nonneg (omegaPositive _).le _)) (by norm_num)
    _ ≤ 2 * (tolerance / (2 * scales.ratio ^ 2) * changed.seed receiver) := finalBound
    _ = tolerance * changed.seed receiver / changed.ratio ^ 2 := by dsimp only [changed]; ring

end EulerNonuniqueness.Paper
