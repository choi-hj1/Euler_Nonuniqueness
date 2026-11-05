import Challenge
import EulerNonuniqueness.Statement

/-!
# Comparison with the independently specified target

The equalities below are checked by Lean's kernel, including the actual
instances elaborated independently in the Mathlib-only challenge module.
These are statement comparisons, not proofs that either target holds.
-/

namespace EulerNonuniquenessComparator

theorem kernel_eq (position : ℂ) :
    EulerNonuniqueness.biotSavartKernel position =
      EulerNonuniquenessChallenge.kernel position := rfl

theorem velocity_eq (vorticity : ℂ → ℝ) :
    EulerNonuniqueness.biotSavart vorticity =
      EulerNonuniquenessChallenge.velocity vorticity := rfl

theorem scalar_test_iff (horizon : ℝ) (test : ℝ × ℂ → ℝ) :
    EulerNonuniqueness.ScalarTestOn horizon test ↔
      EulerNonuniquenessChallenge.ScalarTest horizon test := Iff.rfl

theorem vector_test_iff (horizon : ℝ) (test : ℝ × ℂ → ℂ) :
    EulerNonuniqueness.VectorTestOn horizon test ↔
      EulerNonuniquenessChallenge.VectorTest horizon test := Iff.rfl

theorem transport_iff (initial : ℂ → ℝ) (omega : ℝ → ℂ → ℝ)
    (velocity : ℝ → ℂ → ℂ) :
    EulerNonuniqueness.WeakTransport initial omega velocity ↔
      EulerNonuniquenessChallenge.Transport initial omega velocity := Iff.rfl

theorem momentum_iff (initialVelocity : ℂ → ℂ) (velocity : ℝ → ℂ → ℂ) :
    EulerNonuniqueness.WeakMomentum initialVelocity velocity ↔
      EulerNonuniquenessChallenge.Momentum initialVelocity velocity := Iff.rfl

theorem solution_iff (initial : ℂ → ℝ) (omega : ℝ → ℂ → ℝ) :
    EulerNonuniqueness.IsEulerSolution initial omega ↔
      EulerNonuniquenessChallenge.Solution initial omega := Iff.rfl

theorem target_eq :
    EulerNonuniqueness.Theorem11 = EulerNonuniquenessChallenge.Target := rfl

theorem target_iff :
    EulerNonuniqueness.Theorem11 ↔ EulerNonuniquenessChallenge.Target := Iff.rfl

end EulerNonuniquenessComparator
