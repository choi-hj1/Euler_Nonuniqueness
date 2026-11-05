import EulerNonuniqueness.Section3.RelabeledPrimitiveMovingTerm
import Mathlib.Analysis.Calculus.SmoothSeries

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace

theorem relabeledDiskForcingPrimitive_norm_le_weight48 (degree : ℕ) {frequency : ℝ}
    (nonzero : frequency ≠ 0) (amplitude : ℝ → ℂ) (time : ℝ) (angular : PeriodicC1HolderHalf)
    (bounded : ‖diskRelabelCurve angular 1‖ ≤ 3) :
    ‖relabeledDiskForcingPrimitive angular degree frequency amplitude time‖ ≤
      (2 / |frequency|) * ((48 : ℝ) ^ (degree + 1) * ‖amplitude time‖) := by
  have modeBound : ‖relabeledDiskForcingMode angular degree‖ ≤ (24 : ℝ) ^ (degree + 1) := by
    have actual := rotatedExteriorPower_norm_bound (1 : Circle) (diskRelabelCurve angular 1) bounded degree 1
    simpa only [rotatedExteriorPower, OneMemClass.coe_one, inv_one, one_pow, mul_one, one_smul,
      norm_one, relabeledDiskForcingMode] using actual
  have mode48 := modeBound.trans (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 24) (by norm_num : (24 : ℝ) ≤ 48) _)
  rw [relabeledDiskForcingPrimitive, norm_smul, norm_mul, norm_mul, diskForcingPhase_norm, mul_one]
  exact (mul_le_mul
    (mul_le_mul_of_nonneg_right (diskForcingPrimitiveFactor_norm_le nonzero degree) (norm_nonneg _))
    mode48 (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem relabeledForcingPrimitiveSeries_hasDerivAt_moving_series
    {frequency left right initial time speed : ℝ} (nonzero : frequency ≠ 0)
    (amplitude amplitudeDerivative : ℕ → ℝ → ℂ) (amplitudeBound derivativeBound : ℕ → ℝ)
    (angular baseVelocity : ℝ → PeriodicC1HolderHalf)
    (amplitudeEquation : ∀ degree current, current ∈ Ioo left right →
      HasDerivAt (amplitude degree) (amplitudeDerivative degree current) current)
    (baseEquation : ∀ current, current ∈ Ioo left right →
      HasDerivAt (fun later => diskRelabelCurve (angular later) 1) (baseVelocity current) current)
    (bounds : ∀ degree current, current ∈ Ioo left right →
      ‖amplitude degree current‖ ≤ amplitudeBound degree ∧ ‖amplitudeDerivative degree current‖ ≤ derivativeBound degree)
    (baseBounds : ∀ current, current ∈ Ioo left right →
      ‖diskRelabelCurve (angular current) 1‖ < 3 ∧ ‖baseVelocity current‖ ≤ speed)
    (summableAmplitude : Summable (fun degree => (48 : ℝ) ^ (degree + 1) * amplitudeBound degree))
    (summableDerivative : Summable (fun degree => (48 : ℝ) ^ (degree + 1) * derivativeBound degree))
    (initialMember : initial ∈ Ioo left right) (member : time ∈ Ioo left right) :
    HasDerivAt (fun current => relabeledForcingPrimitiveSeries (angular current) frequency amplitude current)
      (∑' degree, relabeledPrimitiveMovingTermJet degree frequency (amplitude degree) (amplitudeDerivative degree)
        time (angular time) (baseVelocity time)) time := by
  have speedNonnegative : 0 ≤ speed := (norm_nonneg _).trans (baseBounds initial initialMember).2
  have amplitudeNonnegative (degree : ℕ) : 0 ≤ amplitudeBound degree :=
    (norm_nonneg _).trans (bounds degree initial initialMember).1
  have derivativeNonnegative (degree : ℕ) : 0 ≤ derivativeBound degree :=
    (norm_nonneg _).trans (bounds degree initial initialMember).2
  let envelope := fun degree =>
    (2 / |frequency|) * ((48 : ℝ) ^ (degree + 1) * derivativeBound degree) +
      (2 + (2 / |frequency|) * speed) * ((48 : ℝ) ^ (degree + 1) * amplitudeBound degree)
  have summableEnvelope : Summable envelope :=
    (summableDerivative.mul_left _).add (summableAmplitude.mul_left _)
  have initialSummable : Summable (fun degree =>
      relabeledDiskForcingPrimitive (angular initial) degree frequency (amplitude degree) initial) := by
    apply Summable.of_norm_bounded _ (summableAmplitude.mul_left (2 / |frequency|))
    intro degree
    exact (relabeledDiskForcingPrimitive_norm_le_weight48 degree nonzero (amplitude degree) initial
      (angular initial) (baseBounds initial initialMember).1.le).trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (bounds degree initial initialMember).1 (by positivity)) (by positivity))
  unfold relabeledForcingPrimitiveSeries
  apply hasDerivAt_tsum_of_isPreconnected summableEnvelope isOpen_Ioo (convex_Ioo left right).isPreconnected
    (fun degree current currentMember => relabeledPrimitiveMovingTerm_hasDerivAt degree frequency current
      (amplitudeEquation degree current currentMember) (baseEquation current currentMember)
      (baseBounds current currentMember).1)
    ?_ initialMember initialSummable member
  intro degree current currentMember
  have actual := relabeledPrimitiveMovingTermJet_norm_le degree nonzero (amplitude degree)
    (amplitudeDerivative degree) current (angular current) (baseVelocity current) (baseBounds current currentMember).1.le
  apply actual.trans
  dsimp only [envelope]
  calc
    _ ≤ ((2 / |frequency|) * derivativeBound degree +
        (2 + (2 / |frequency|) * speed) * amplitudeBound degree) * (48 : ℝ) ^ (degree + 1) := by
      gcongr
      · exact (bounds degree current currentMember).2
      · exact (baseBounds current currentMember).2
      · exact (bounds degree current currentMember).1
    _ = _ := by ring

theorem summable_relabeledPrimitiveMovingTermJet {frequency : ℝ} (nonzero : frequency ≠ 0)
    (amplitude amplitudeDerivative : ℕ → ℝ → ℂ) (time : ℝ)
    (angular baseVelocity : PeriodicC1HolderHalf) (bounded : ‖diskRelabelCurve angular 1‖ ≤ 3)
    (weighted : Summable (fun degree => (48 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖))
    (derivativeWeighted : Summable (fun degree => (48 : ℝ) ^ (degree + 1) * ‖amplitudeDerivative degree time‖)) :
    Summable (fun degree => relabeledPrimitiveMovingTermJet degree frequency
      (amplitude degree) (amplitudeDerivative degree) time angular baseVelocity) := by
  have envelope := (derivativeWeighted.mul_left (2 / |frequency|)).add
    (weighted.mul_left (2 + (2 / |frequency|) * ‖baseVelocity‖))
  apply Summable.of_norm_bounded _ envelope
  intro degree
  exact (relabeledPrimitiveMovingTermJet_norm_le degree nonzero (amplitude degree)
    (amplitudeDerivative degree) time angular baseVelocity bounded).trans_eq (by ring)

theorem relabeledForcingPrimitiveSeries_hasDerivAt_moving_of_frozen
    {frequency left right initial time speed : ℝ} (nonzero : frequency ≠ 0)
    (amplitude amplitudeDerivative : ℕ → ℝ → ℂ) (amplitudeBound derivativeBound : ℕ → ℝ)
    (angular baseVelocity : ℝ → PeriodicC1HolderHalf)
    (amplitudeEquation : ∀ degree current, current ∈ Ioo left right →
      HasDerivAt (amplitude degree) (amplitudeDerivative degree current) current)
    (baseEquation : ∀ current, current ∈ Ioo left right →
      HasDerivAt (fun later => diskRelabelCurve (angular later) 1) (baseVelocity current) current)
    (bounds : ∀ degree current, current ∈ Ioo left right →
      ‖amplitude degree current‖ ≤ amplitudeBound degree ∧ ‖amplitudeDerivative degree current‖ ≤ derivativeBound degree)
    (baseBounds : ∀ current, current ∈ Ioo left right →
      ‖diskRelabelCurve (angular current) 1‖ < 3 ∧ ‖baseVelocity current‖ ≤ speed)
    (summableAmplitude : Summable (fun degree => (48 : ℝ) ^ (degree + 1) * amplitudeBound degree))
    (summableDerivative : Summable (fun degree => (48 : ℝ) ^ (degree + 1) * derivativeBound degree))
    (initialMember : initial ∈ Ioo left right) (member : time ∈ Ioo left right)
    (weighted : Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖))
    {frozenVelocity : PeriodicC1HolderHalf}
    (frozenActual : HasDerivAt (fun current =>
      relabeledForcingPrimitiveSeries (angular time) frequency amplitude current) frozenVelocity time) :
    HasDerivAt (fun current => relabeledForcingPrimitiveSeries (angular current) frequency amplitude current)
      (frozenVelocity + exteriorContourPowerSeriesFirstJet (Circle.exp (frequency * time / 2))
        (fun degree => diskForcingPrimitiveFactor degree frequency * amplitude degree time)
        (diskRelabelCurve (angular time) 1) (baseVelocity time)) time := by
  have moving := relabeledForcingPrimitiveSeries_hasDerivAt_moving_series nonzero amplitude amplitudeDerivative
    amplitudeBound derivativeBound angular baseVelocity amplitudeEquation baseEquation bounds baseBounds
    summableAmplitude summableDerivative initialMember member
  have frozen := relabeledForcingPrimitiveSeries_hasDerivAt_moving_series (speed := 0) nonzero amplitude amplitudeDerivative
    amplitudeBound derivativeBound (fun _ => angular time) (fun _ => 0) amplitudeEquation
    (fun current _ => hasDerivAt_const current (diskRelabelCurve (angular time) 1)) bounds
    (fun _ _ => ⟨(baseBounds time member).1, by simp⟩)
    summableAmplitude summableDerivative initialMember member
  simp only [relabeledPrimitiveMovingTermJet, map_zero, add_zero] at frozen
  have scalarIdentity := frozen.unique frozenActual
  have actual48 := summable_exteriorCoefficientWeight_mono (fun degree => amplitude degree time)
    (by norm_num : (0 : ℝ) ≤ 48) (by norm_num : (48 : ℝ) ≤ 96) weighted
  have derivative48 : Summable (fun degree => (48 : ℝ) ^ (degree + 1) * ‖amplitudeDerivative degree time‖) :=
    Summable.of_nonneg_of_le (fun degree => by positivity)
      (fun degree => mul_le_mul_of_nonneg_left (bounds degree time member).2 (by positivity)) summableDerivative
  have scalarSummable := summable_relabeledPrimitiveMovingTermJet nonzero amplitude amplitudeDerivative time
    (angular time) 0 (baseBounds time member).1.le actual48 derivative48
  simp only [relabeledPrimitiveMovingTermJet, map_zero, add_zero] at scalarSummable
  have coefficient96 := summable_relabeledPrimitiveCoefficient_weight96 nonzero amplitude time weighted
  have coefficient48 := summable_exteriorCoefficientWeight_mono
    (fun degree => diskForcingPrimitiveFactor degree frequency * amplitude degree time)
    (by norm_num : (0 : ℝ) ≤ 48) (by norm_num : (48 : ℝ) ≤ 96) coefficient96
  have operatorSummable := exteriorContourPowerSeriesFirstJet_summable (Circle.exp (frequency * time / 2))
    (fun degree => diskForcingPrimitiveFactor degree frequency * amplitude degree time)
    (diskRelabelCurve (angular time) 1) (baseBounds time member).1.le coefficient48
  have appliedSum := (ContinuousLinearMap.apply ℝ PeriodicC1HolderHalf (baseVelocity time)).hasSum operatorSummable.hasSum
  have appliedSumActual : HasSum (fun degree => rotatedExteriorPowerFirstJet (Circle.exp (frequency * time / 2))
      (diskRelabelCurve (angular time) 1) degree
      (diskForcingPrimitiveFactor degree frequency * amplitude degree time) (baseVelocity time))
      (exteriorContourPowerSeriesFirstJet (Circle.exp (frequency * time / 2))
        (fun degree => diskForcingPrimitiveFactor degree frequency * amplitude degree time)
        (diskRelabelCurve (angular time) 1) (baseVelocity time)) := by
    simpa only [ContinuousLinearMap.apply_apply, exteriorContourPowerSeriesFirstJet] using appliedSum
  have sumIdentity : (∑' degree, relabeledPrimitiveMovingTermJet degree frequency
      (amplitude degree) (amplitudeDerivative degree) time (angular time) (baseVelocity time)) =
      frozenVelocity + exteriorContourPowerSeriesFirstJet (Circle.exp (frequency * time / 2))
        (fun degree => diskForcingPrimitiveFactor degree frequency * amplitude degree time)
        (diskRelabelCurve (angular time) 1) (baseVelocity time) := by
    unfold relabeledPrimitiveMovingTermJet
    rw [Summable.tsum_add scalarSummable appliedSumActual.summable, scalarIdentity, appliedSumActual.tsum_eq]
  rw [sumIdentity] at moving
  exact moving

end EulerNonuniqueness.Paper
