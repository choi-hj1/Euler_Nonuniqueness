import EulerNonuniqueness.Section1.ExternalFieldScaleBounds
import EulerNonuniqueness.Section1.DyadicSeparation
import EulerNonuniqueness.Section1.UniformScaleBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- The outgoing branch is affine; no continuity at an incoming/outgoing switch is asserted. -/
theorem Scales.eventually_outgoing_short_source_action_small (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {outgoing span tolerance : ℝ} (outgoingNonnegative : 0 ≤ outgoing)
    (_spanNonnegative : 0 ≤ span) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ, ∀ selected : Finset ℕ,
    (∀ source ∈ selected, index + 1 ≤ source) →
    ∀ entry distance neutral : ℕ → ℝ, ∀ start finish rate : ℝ,
    0 ≤ start → start ≤ finish → finish ≤ 1 →
    (∀ source ∈ selected, 0 ≤ entry source ∧ entry source ≤ start) →
    let changed : Scales := {scales with frequency := frequency}
    (∀ source ∈ selected, 0 ≤ distance source ∧ distance source ≤ changed.omega source / 16) →
    (∀ source ∈ selected, 0 ≤ neutral source ∧ neutral source ≤ changed.length source ^ 2) →
    0 ≤ rate → rate ≤ changed.omega index → changed.omega index * (finish - start) ≤ span →
    let sourceEnvelope := fun time => ∑ source ∈ selected,
      outgoing * changed.circulation source * (changed.circulation source * (time - entry source) +
        (1 + distance source) * changed.length source ^ 2 + neutral source)
    Continuous sourceEnvelope ∧
    IntervalIntegrable (fun time => Real.exp (rate * (finish - time)) * sourceEnvelope time) volume start finish ∧
    (∫ time in start..finish, Real.exp (rate * (finish - time)) * sourceEnvelope time) / changed.location index ^ 4 ≤
      4 * outgoing * Real.exp span * changed.strain ^ 2 ∧
    (∫ time in start..finish, Real.exp (rate * (finish - time)) * sourceEnvelope time) / changed.location index ^ 4 ≤ tolerance := by
  have decay := ((scales.strain_tendsto_zero ratioBound alphaPositive).pow 2).const_mul
    (4 * outgoing * Real.exp span)
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at decay
  filter_upwards [eventually_ge_atTop (1 : ℝ), decay.eventually (eventually_lt_nhds tolerancePositive)]
    with frequency frequencyOne small
  intro index selected selectedBounds entry distance neutral start finish rate startNonnegative startFinish finishOne entries
  dsimp only
  intro distances neutrals rateNonnegative rateBound ageBound
  let changed : Scales := {scales with frequency := frequency}
  let sourceEnvelope := fun time => ∑ source ∈ selected,
    outgoing * changed.circulation source * (changed.circulation source * (time - entry source) +
      (1 + distance source) * changed.length source ^ 2 + neutral source)
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have circulationPositive (source : ℕ) := changed.circulation_pos frequencyPositive ratioPositive source
  have omegaPositive (source : ℕ) := changed.omega_pos frequencyPositive ratioPositive source
  have omegaOne (source : ℕ) : 1 ≤ changed.omega source := frequencyOne.trans
    (changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith only [ratioBound]) source)
  have lengthCost (source : ℕ) : changed.length source ^ 2 ≤ changed.circulation source ∧
      changed.omega source * changed.length source ^ 2 ≤ changed.circulation source := by
    have piBound : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have scaled := mul_le_mul_of_nonneg_right piBound
      (mul_nonneg (omegaPositive source).le (sq_nonneg (changed.length source)))
    have identity : changed.circulation source = 2 * Real.pi *
        (changed.omega source * changed.length source ^ 2) := by rw [Scales.circulation]; ring
    rw [← identity] at scaled
    have omegaCost : changed.omega source * changed.length source ^ 2 ≤ changed.circulation source := by
      simpa only [one_mul] using scaled
    have lengthBound := mul_le_mul_of_nonneg_right (omegaOne source) (sq_nonneg (changed.length source))
    simp only [one_mul] at lengthBound
    exact ⟨lengthBound.trans omegaCost, omegaCost⟩
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (circulationPositive _).le (sq_nonneg _)
  have total : (∑ source ∈ selected, changed.circulation source / changed.location source ^ 2) ≤ changed.strain := by
    have shifted : (∑ source ∈ selected, changed.circulation source / changed.location source ^ 2) =
        ∑ next ∈ selected.image (fun source => source - 1),
          changed.circulation (next + 1) / changed.location (next + 1) ^ 2 := by
      rw [Finset.sum_image (by
        intro first firstInside second secondInside equal
        have firstPositive := selectedBounds first firstInside
        have secondPositive := selectedBounds second secondInside
        omega)]
      apply Finset.sum_congr rfl
      intro source member
      rw [Nat.sub_add_cancel (by have := selectedBounds source member; omega)]
    rw [shifted]
    exact (changed.circulation_location_summable frequencyOne ratioBound alphaPositive 2).sum_le_tsum
      _ (fun source _ => div_nonneg (circulationPositive _).le (sq_nonneg _))
  have quadratic : (∑ source ∈ selected, changed.circulation source ^ 2) ≤ changed.location index ^ 4 * changed.strain ^ 2 := by
    have weighted := Finset.sum_sq_le_sq_sum_of_nonneg (s := selected)
      (f := fun source => changed.circulation source / changed.location source ^ 2)
      (fun source _ => div_nonneg (circulationPositive _).le (sq_nonneg _))
    have squares := (pow_le_pow_left₀ (Finset.sum_nonneg (fun source _ =>
      div_nonneg (circulationPositive _).le (sq_nonneg _))) total 2)
    calc
      _ ≤ ∑ source ∈ selected, changed.location index ^ 4 *
          (changed.circulation source / changed.location source ^ 2) ^ 2 := by
        apply Finset.sum_le_sum
        intro source member
        have order : changed.location source ≤ changed.location index := changed.location_antitone (by
          have := selectedBounds source member; omega)
        have scaled := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (changed.location_pos source).le order 4)
          (sq_nonneg (changed.circulation source / changed.location source ^ 2))
        have identity : changed.location source ^ 4 * (changed.circulation source / changed.location source ^ 2) ^ 2 =
            changed.circulation source ^ 2 := by field_simp [(changed.location_pos source).ne']; ring
        rw [identity] at scaled
        exact scaled
      _ = changed.location index ^ 4 * ∑ source ∈ selected,
          (changed.circulation source / changed.location source ^ 2) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ changed.location index ^ 4 * changed.strain ^ 2 :=
        mul_le_mul_of_nonneg_left (weighted.trans squares) (pow_nonneg (changed.location_pos _).le 4)
  have sourceBound (time : ℝ) (inside : time ∈ Icc start finish) :
      sourceEnvelope time ≤ 4 * outgoing * changed.location index ^ 4 * changed.strain ^ 2 := by
    have each (source : ℕ) (member : source ∈ selected) :
        outgoing * changed.circulation source * (changed.circulation source * (time - entry source) +
          (1 + distance source) * changed.length source ^ 2 + neutral source) ≤
        4 * outgoing * changed.circulation source ^ 2 := by
      have age : time - entry source ≤ 1 := by linarith only [inside.2, finishOne, (entries source member).1]
      have distanceBound : distance source ≤ changed.omega source := by
        linarith only [(distances source member).2, omegaPositive source]
      have distanceCost := (mul_le_mul_of_nonneg_right distanceBound (sq_nonneg (changed.length source))).trans (lengthCost source).2
      have neutralCost := (neutrals source member).2.trans (lengthCost source).1
      have numerator : changed.circulation source * (time - entry source) +
          (1 + distance source) * changed.length source ^ 2 + neutral source ≤ 4 * changed.circulation source := by
        nlinarith only [mul_le_mul_of_nonneg_left age (circulationPositive source).le,
          distanceCost, neutralCost, (lengthCost source).1]
      have scaled := mul_le_mul_of_nonneg_left numerator (mul_nonneg outgoingNonnegative (circulationPositive source).le)
      convert scaled using 1; ring
    calc
      _ ≤ ∑ source ∈ selected, 4 * outgoing * changed.circulation source ^ 2 := Finset.sum_le_sum each
      _ = 4 * outgoing * ∑ source ∈ selected, changed.circulation source ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 4 * outgoing * (changed.location index ^ 4 * changed.strain ^ 2) :=
        mul_le_mul_of_nonneg_left quadratic (by positivity)
      _ = _ := by ring
  have sourceContinuous : Continuous sourceEnvelope := by unfold sourceEnvelope; fun_prop
  have kernelContinuous : Continuous (fun time : ℝ => Real.exp (rate * (finish - time))) := by fun_prop
  have integrable := (kernelContinuous.mul sourceContinuous).intervalIntegrable (μ := volume) start finish
  have kernelBound (time : ℝ) (inside : time ∈ Icc start finish) : Real.exp (rate * (finish - time)) ≤ Real.exp span := by
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_left inside.1 finish) rateNonnegative).trans
      ((mul_le_mul_of_nonneg_right rateBound (sub_nonneg.mpr startFinish)).trans ageBound)
  have pointwise (time : ℝ) (inside : time ∈ Icc start finish) :
      Real.exp (rate * (finish - time)) * sourceEnvelope time ≤
        Real.exp span * (4 * outgoing * changed.location index ^ 4 * changed.strain ^ 2) :=
    (mul_le_mul_of_nonneg_left (sourceBound time inside) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_right (kernelBound time inside) (by positivity))
  have integralBound := intervalIntegral.integral_mono_on startFinish integrable
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Real.exp span *
      (4 * outgoing * changed.location index ^ 4 * changed.strain ^ 2)) volume start finish) pointwise
  rw [intervalIntegral.integral_const, smul_eq_mul] at integralBound
  have ageOne : finish - start ≤ 1 := by linarith only [startNonnegative, finishOne]
  have finalBound := integralBound.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ageOne
      (show 0 ≤ Real.exp span * (4 * outgoing * changed.location index ^ 4 * changed.strain ^ 2) by positivity))
  have divided := div_le_div_of_nonneg_right finalBound (pow_nonneg (changed.location_pos index).le 4)
  have normalized : (∫ time in start..finish, Real.exp (rate * (finish - time)) * sourceEnvelope time) /
      changed.location index ^ 4 ≤ 4 * outgoing * Real.exp span * changed.strain ^ 2 := by
    convert divided using 1; field_simp [(changed.location_pos index).ne']; ring
  exact ⟨sourceContinuous, integrable, normalized, normalized.trans small.le⟩

end EulerNonuniqueness.Paper
