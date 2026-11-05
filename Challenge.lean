import Mathlib

/-!
# Independent mathematical target: manuscript Theorem 1.1

This module imports only Mathlib. It independently specifies the actual
Lebesgue spaces, Biot–Savart law, distributional identities, initial traces,
and quantifiers. `Target` independently specifies the theorem's conclusion
without assuming it. `Comparator.lean` checks it against the implementation.

The plane is `ℂ` with its Euclidean norm and Lebesgue measure. Time is real,
and only nonnegative times are constrained. Smooth means order `∞`;
analytic order `ω` is deliberately not used for compactly supported tests.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open scoped ContDiff

namespace EulerNonuniquenessChallenge

abbrev Vorticity := ℂ → ℝ
abbrev Evolution := ℝ → ℂ → ℝ
abbrev VelocityEvolution := ℝ → ℂ → ℂ

def kernel (position : ℂ) : ℂ :=
  Complex.I * position / ((2 * Real.pi * ‖position‖ ^ 2 : ℝ) : ℂ)

def velocity (vorticity : Vorticity) : ℂ → ℂ :=
  fun position => ∫ source, vorticity source • kernel (position - source)

def ScalarTest (horizon : ℝ) (test : ℝ × ℂ → ℝ) : Prop :=
  ContDiff ℝ ∞ test ∧ HasCompactSupport test ∧
    ∀ time position, horizon ≤ time → test (time, position) = 0

def VectorTest (horizon : ℝ) (test : ℝ × ℂ → ℂ) : Prop :=
  ContDiff ℝ ∞ test ∧ HasCompactSupport test ∧
    (∀ time position, horizon ≤ time → test (time, position) = 0) ∧
    ∀ point,
      (fderiv ℝ test point (0, 1)).re +
        (fderiv ℝ test point (0, Complex.I)).im = 0

def StrongLpContinuous {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] [MeasurableSpace Value] [BorelSpace Value]
    (exponent : ℝ≥0∞) (field : ℝ → ℂ → Value) : Prop :=
  ∃ exponentBound : 1 ≤ exponent,
    letI : Fact (1 ≤ exponent) := ⟨exponentBound⟩
    ∃ membership : ∀ time : ℝ≥0, MemLp (field time) exponent volume,
      Continuous (fun time : ℝ≥0 => (membership time).toLp (field time))

def Transport (initial : Vorticity) (omega : Evolution)
    (field : VelocityEvolution) : Prop :=
  ∀ horizon : ℝ, 0 < horizon → ∀ test, ScalarTest horizon test →
    let measure : Measure (ℝ × ℂ) := (volume.restrict (Ioo 0 horizon)).prod volume
    let integrand := fun point : ℝ × ℂ =>
      omega point.1 point.2 *
        (fderiv ℝ test point (1, 0) + fderiv ℝ test point (0, field point.1 point.2))
    Integrable integrand measure ∧
    Integrable (fun position => initial position * test (0, position)) ∧
    (∫ point, integrand point ∂measure) +
      (∫ position, initial position * test (0, position)) = 0

def Momentum (initialVelocity : ℂ → ℂ) (field : VelocityEvolution) : Prop :=
  ∀ horizon : ℝ, 0 < horizon → ∀ test, VectorTest horizon test →
    let measure : Measure (ℝ × ℂ) := (volume.restrict (Ioo 0 horizon)).prod volume
    let integrand := fun point : ℝ × ℂ =>
      @inner ℝ ℂ _ (field point.1 point.2)
        (fderiv ℝ test point (1, 0) + fderiv ℝ test point (0, field point.1 point.2))
    Integrable integrand measure ∧
    Integrable (fun position => @inner ℝ ℂ _ (initialVelocity position) (test (0, position))) ∧
    (∫ point, integrand point ∂measure) +
      (∫ position, @inner ℝ ℂ _ (initialVelocity position) (test (0, position))) = 0

def Solution (initial : Vorticity) (omega : Evolution) : Prop :=
  (omega 0 =ᵐ[volume] initial) ∧
    (∀ exponent : ℝ, 1 ≤ exponent → StrongLpContinuous (ENNReal.ofReal exponent) omega) ∧
    StrongLpContinuous 2 (fun time => velocity (omega time)) ∧
    (∀ time : ℝ, 0 ≤ time → ∀ᵐ position ∂(volume : Measure ℂ),
      Integrable (fun source => omega time source • kernel (position - source))) ∧
    (∀ exponent : ℝ, 1 ≤ exponent → ∀ time : ℝ, 0 ≤ time →
      eLpNorm (omega time) (ENNReal.ofReal exponent) volume =
        eLpNorm initial (ENNReal.ofReal exponent) volume) ∧
    (∀ time : ℝ, 0 ≤ time → ∀ test : ℂ → ℝ,
      ContDiff ℝ ∞ test → HasCompactSupport test →
      Integrable (fun position => fderiv ℝ test position (velocity (omega time) position)) ∧
      (∫ position, fderiv ℝ test position (velocity (omega time) position)) = 0) ∧
    Transport initial omega (fun time => velocity (omega time)) ∧
    (∀ renormalization : ℝ → ℝ,
      (ContDiff ℝ 1 renormalization ∧
        ∃ bound : ℝ, 0 ≤ bound ∧ ∀ value, |deriv renormalization value| ≤ bound) →
      Transport (renormalization ∘ initial)
        (fun time => renormalization ∘ omega time) (fun time => velocity (omega time))) ∧
    Momentum (velocity initial) (fun time => velocity (omega time))

def Target : Prop :=
  ∃ initial : Vorticity, ∃ first second : Evolution,
    (HasCompactSupport initial ∧
      (∀ exponent : ℝ, 1 ≤ exponent → MemLp initial (ENNReal.ofReal exponent) volume) ∧
      (∫ position, initial position) = 0) ∧
    Solution initial first ∧
    Solution initial second ∧
    0 < ∫ position, |second 1 position - first 1 position|

end EulerNonuniquenessChallenge
