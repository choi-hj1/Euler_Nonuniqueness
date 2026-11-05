import EulerNonuniqueness.Section4.ReferenceStatement
import EulerNonuniqueness.Section3.HolderPaperBoundaryBound

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem ReferenceCoarseBounds.mono_constant {count : ℕ} {scales : Scales} {motion : PatchMotion count}
    {threshold first second : ℝ} (coarse : ReferenceCoarseBounds scales motion threshold first)
    (firstNonnegative : 0 ≤ first) (ordered : first ≤ second)
    (strainNonnegative : 0 ≤ scales.strain) (hessianNonnegative : 0 ≤ scales.hessian) :
    ReferenceCoarseBounds scales motion threshold second := by
  have secondNonnegative : 0 ≤ second := firstNonnegative.trans ordered
  refine ⟨coarse.1, ?_, coarse.2.2⟩
  intro time member index
  obtain ⟨unstable, stable, lower, upper, memory, boundary⟩ := coarse.2.1 time member index
  refine ⟨unstable, stable, lower, upper, memory.trans ?_, ?_⟩
  · have timeNonnegative := member.1
    gcongr
  · intro patch
    obtain ⟨relabeling, periodic, relabelingBound, errorBound⟩ := boundary patch
    exact ⟨relabeling, periodic, relabelingBound,
      errorBound.mono (mul_le_mul_of_nonneg_right ordered (sq_nonneg _))⟩

theorem ReferenceSharpBounds.mono_constant {count : ℕ} {scales : Scales} {motion : PatchMotion count}
    {phase : Fin count → ℝ} {phaseLift : ℝ → Fin count → ℝ} {first second : ℝ}
    (sharp : ReferenceSharpBounds scales motion phase phaseLift first) (ordered : first ≤ second)
    (strainNonnegative : 0 ≤ scales.strain) (outerNonnegative : 0 ≤ scales.outerDisplacementBound)
    (frequencyPositive : ∀ index : Fin count, 0 < scales.omega (index.val + 1)) :
    ReferenceSharpBounds scales motion phase phaseLift second := by
  constructor
  · intro terminal terminalPositive terminalBound time member index
    obtain ⟨shape, phaseBound⟩ := sharp.1 terminal terminalPositive terminalBound time member index
    have omegaPositive := frequencyPositive index
    constructor
    · exact shape.trans (mul_le_mul_of_nonneg_right ordered (by positivity))
    · exact phaseBound.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ordered terminalPositive.le) (by positivity))
  · intro time member index outer
    exact (sharp.2 time member index outer).trans (mul_le_mul_of_nonneg_right ordered outerNonnegative)

end EulerNonuniqueness.Paper
