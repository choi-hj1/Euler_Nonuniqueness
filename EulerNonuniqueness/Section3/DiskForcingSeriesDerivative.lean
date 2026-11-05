import EulerNonuniqueness.Section3.DiskForcingPrimitiveSeries
import Mathlib.Analysis.Calculus.SmoothSeries

namespace EulerNonuniqueness.Paper

noncomputable section

open Set

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance forcingSeriesDerivativeC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

def diskForcingPrimitiveJet (degree : ℕ) (frequency : ℝ)
    (amplitude amplitudeDerivative : ℝ → ℂ) (time : ℝ) : PeriodicC1HolderHalf :=
  frequency • diskRotatingDerivative (diskForcingPrimitive degree frequency amplitude time) +
    (amplitude time * diskForcingPhase degree frequency time) • c1Conjugate (diskCircleMode (degree + 1)) +
    diskForcingPrimitive degree frequency amplitudeDerivative time

theorem diskForcingPrimitiveJet_norm_bound (degree : ℕ) {frequency : ℝ}
    (nonzero : frequency ≠ 0) (amplitude amplitudeDerivative : ℝ → ℂ) (time : ℝ) :
    ‖diskForcingPrimitiveJet degree frequency amplitude amplitudeDerivative time‖ ≤
      ((2 * ‖diskRotatingDerivative‖ + 1) * ‖amplitude time‖ +
        (2 / |frequency|) * ‖amplitudeDerivative time‖) *
          ‖c1Conjugate (diskCircleMode (degree + 1))‖ := by
  have frequencyPositive : 0 < |frequency| := abs_pos.mpr nonzero
  have degreePositive : (1 : ℝ) ≤ ((degree + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le degree)
  have factorBound : 2 / (((degree + 1 : ℕ) : ℝ) * |frequency|) ≤ 2 / |frequency| := by
    apply div_le_div_of_nonneg_left (by norm_num) frequencyPositive
    nlinarith
  have primitiveBound (current : ℝ → ℂ) :
      ‖diskForcingPrimitive degree frequency current time‖ ≤
        (2 / |frequency|) * ‖current time‖ * ‖c1Conjugate (diskCircleMode (degree + 1))‖ := by
    rw [diskForcingPrimitive_norm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right factorBound (norm_nonneg _)) (norm_nonneg _)
  have first := norm_smul_le frequency (diskRotatingDerivative (diskForcingPrimitive degree frequency amplitude time))
  have operator := diskRotatingDerivative.le_opNorm (diskForcingPrimitive degree frequency amplitude time)
  have mainBound : ‖frequency • diskRotatingDerivative (diskForcingPrimitive degree frequency amplitude time)‖ ≤
      2 * ‖diskRotatingDerivative‖ * ‖amplitude time‖ * ‖c1Conjugate (diskCircleMode (degree + 1))‖ := by
    calc
      _ ≤ |frequency| * (‖diskRotatingDerivative‖ * ‖diskForcingPrimitive degree frequency amplitude time‖) :=
        first.trans (mul_le_mul_of_nonneg_left operator (abs_nonneg _))
      _ ≤ |frequency| * (‖diskRotatingDerivative‖ *
          ((2 / |frequency|) * ‖amplitude time‖ * ‖c1Conjugate (diskCircleMode (degree + 1))‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (primitiveBound amplitude) (norm_nonneg _)) (abs_nonneg _)
      _ = _ := by field_simp; ring
  have forcingNorm : ‖(amplitude time * diskForcingPhase degree frequency time) •
      c1Conjugate (diskCircleMode (degree + 1))‖ =
      ‖amplitude time‖ * ‖c1Conjugate (diskCircleMode (degree + 1))‖ := by
    rw [norm_smul, norm_mul, diskForcingPhase_norm, mul_one]
  unfold diskForcingPrimitiveJet
  calc
    _ ≤ ‖frequency • diskRotatingDerivative (diskForcingPrimitive degree frequency amplitude time)‖ +
        ‖(amplitude time * diskForcingPhase degree frequency time) • c1Conjugate (diskCircleMode (degree + 1))‖ +
        ‖diskForcingPrimitive degree frequency amplitudeDerivative time‖ := (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ _ := by rw [forcingNorm]; nlinarith [mainBound, primitiveBound amplitudeDerivative]

theorem diskForcingPrimitive_tsum_hasDerivAt {frequency left right initial time : ℝ}
    (nonzero : frequency ≠ 0) (amplitude amplitudeDerivative : ℕ → ℝ → ℂ)
    (amplitudeBound derivativeBound : ℕ → ℝ)
    (amplitudeEquation : ∀ degree current, current ∈ Ioo left right →
      HasDerivAt (amplitude degree) (amplitudeDerivative degree current) current)
    (bounds : ∀ degree current, current ∈ Ioo left right →
      ‖amplitude degree current‖ ≤ amplitudeBound degree ∧
        ‖amplitudeDerivative degree current‖ ≤ derivativeBound degree)
    (summableAmplitude : Summable (fun degree =>
      ‖c1Conjugate (diskCircleMode (degree + 1))‖ * amplitudeBound degree))
    (summableDerivative : Summable (fun degree =>
      ‖c1Conjugate (diskCircleMode (degree + 1))‖ * derivativeBound degree))
    (initialMember : initial ∈ Ioo left right)
    (member : time ∈ Ioo left right) :
    HasDerivAt (fun current => ∑' degree, diskForcingPrimitive degree frequency (amplitude degree) current)
      (∑' degree, diskForcingPrimitiveJet degree frequency (amplitude degree) (amplitudeDerivative degree) time) time := by
  let envelope := fun degree => (2 * ‖diskRotatingDerivative‖ + 1) *
      (‖c1Conjugate (diskCircleMode (degree + 1))‖ * amplitudeBound degree) +
      (2 / |frequency|) * (‖c1Conjugate (diskCircleMode (degree + 1))‖ * derivativeBound degree)
  have summableEnvelope : Summable envelope :=
    (summableAmplitude.mul_left _).add (summableDerivative.mul_left _)
  have initialSummable : Summable (fun degree => diskForcingPrimitive degree frequency (amplitude degree) initial) := by
    apply Summable.of_norm_bounded _ (summableAmplitude.mul_left (2 / |frequency|))
    intro degree
    rw [diskForcingPrimitive_norm]
    have frequencyPositive : 0 < |frequency| := abs_pos.mpr nonzero
    have degreePositive : (1 : ℝ) ≤ ((degree + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le degree)
    have factorBound : 2 / (((degree + 1 : ℕ) : ℝ) * |frequency|) ≤ 2 / |frequency| := by
      apply div_le_div_of_nonneg_left (by norm_num) frequencyPositive
      nlinarith
    have bound := (bounds degree initial initialMember).1
    calc
      _ ≤ (2 / |frequency|) * amplitudeBound degree * ‖c1Conjugate (diskCircleMode (degree + 1))‖ :=
        mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right factorBound (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left bound (by positivity))) (norm_nonneg _)
      _ = _ := by ring
  apply hasDerivAt_tsum_of_isPreconnected summableEnvelope isOpen_Ioo (convex_Ioo left right).isPreconnected
    (fun degree current currentMember => diskForcingPrimitive_hasDerivAt degree nonzero (amplitudeEquation degree current currentMember))
    ?_ initialMember initialSummable member
  intro degree current currentMember
  apply (diskForcingPrimitiveJet_norm_bound degree nonzero (amplitude degree) (amplitudeDerivative degree) current).trans
  dsimp only [envelope]
  have bound := bounds degree current currentMember
  have frequencyPositive : 0 < |frequency| := abs_pos.mpr nonzero
  nlinarith [mul_le_mul_of_nonneg_left bound.1 (show 0 ≤ (2 * ‖diskRotatingDerivative‖ + 1) from by positivity),
    mul_le_mul_of_nonneg_left bound.2 (show 0 ≤ 2 / |frequency| from by positivity),
    norm_nonneg (c1Conjugate (diskCircleMode (degree + 1)))]

end

end EulerNonuniqueness.Paper
