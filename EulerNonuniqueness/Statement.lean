import EulerNonuniqueness.Definitions

/-!
# Referee-facing target: Theorem 1.1 of the manuscript

The manuscript is *Nonuniqueness of Solutions to 2D Incompressible Euler Equations with Unbounded Vorticity*.

Reading guide (all mathematical content of the abbreviations used below):

* `Plane = ℂ = ℝ²`, with Euclidean norm and Lebesgue measure `dx`.
* `Vorticity = Plane → ℝ`; `Evolution = ℝ → Vorticity`; only times `t ≥ 0`
  are constrained. `∃` means “there exist”, and `∧` means “and”.
* `InitialDatum initial`: `initial` has compact support, belongs to `Lᵖ`
  for every real `1 ≤ p < ∞`, and has integral zero.
* For `omega`, put `u(t,x) = ∫ K(x-y) omega(t,y) dy`, where
  `K(z) = i z / (2π|z|²)` for `z ≠ 0`, and `K(0) = 0`.
* `IsEulerSolution initial omega` means ALL of the following:
  `omega(0) = initial` almost everywhere; `omega ∈ C([0,∞);Lᵖ)` for every
  finite `p ≥ 1`; `u ∈ C([0,∞);L²)`; the kernel integral exists almost
  everywhere at each time; `‖omega(t)‖ₚ = ‖initial‖ₚ`; and `div u(t) = 0`.
  For every `T > 0` and smooth compactly supported scalar test `φ` vanishing
  for `t ≥ T`, it also requires the integrable weak transport identity
  `∫₀ᵀ∫ omega (∂t φ + u·∇φ) dx dt + ∫ initial φ(0) dx = 0`.
  The same identity holds with `omega, initial` replaced by `β(omega),
  β(initial)` for every `C¹` function `β : ℝ → ℝ` with bounded derivative.
  For every smooth compactly supported divergence-free vector test `ψ`
  vanishing for `t ≥ T`, weak momentum is the integrable identity
  `∫₀ᵀ∫ u·(∂t ψ + (u·∇)ψ) dx dt + ∫ (K*initial)·ψ(0) dx = 0`.
* `l1Distance f g = ∫ |f(x)-g(x)| dx`.

The imported `Definitions.lean` implements precisely this vocabulary using
Mathlib's actual measure, integral, derivative, and quotient `Lp` spaces.

This declaration specifies the target proposition. `EulerNonuniqueness.theorem11`
in `Theorem11.lean` proves it without hypotheses. `Audit.lean` and `AUDIT_STATUS.md`
document the declarations and trust checks.
-/

namespace EulerNonuniqueness

def Theorem11 : Prop :=
  ∃ initial : Vorticity, ∃ first second : Evolution,
    InitialDatum initial ∧
    IsEulerSolution initial first ∧
    IsEulerSolution initial second ∧
    0 < l1Distance (second 1) (first 1)

end EulerNonuniqueness
