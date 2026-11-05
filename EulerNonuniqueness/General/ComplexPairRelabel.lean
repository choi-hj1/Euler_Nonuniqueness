import EulerNonuniqueness.General.ComplexPairPositiveExtension
import EulerNonuniqueness.General.ComplexPairBilinearExtension

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space]
  [NormedSpace ℂ Space] [NormedSpace ℝ Space]
  [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]

theorem complexPairReal_linear_relabel (conjugate linear : Space →L[ℝ] Space)
    (complexLinear : ∀ (scalar : ℂ) vector, linear (scalar • vector) = scalar • linear vector)
    (commutes : ∀ vector, conjugate (linear vector) = linear (conjugate vector)) (pair : Space × Space) :
    complexPairReal conjugate (linear pair.1, linear pair.2) = linear (complexPairReal conjugate pair) := by
  change (1 / 2 : ℂ) • (linear pair.1 + conjugate (linear pair.2)) =
    linear ((1 / 2 : ℂ) • (pair.1 + conjugate pair.2))
  rw [commutes, complexLinear, map_add]

theorem complexPairImaginary_linear_relabel (conjugate linear : Space →L[ℝ] Space)
    (complexLinear : ∀ (scalar : ℂ) vector, linear (scalar • vector) = scalar • linear vector)
    (commutes : ∀ vector, conjugate (linear vector) = linear (conjugate vector)) (pair : Space × Space) :
    complexPairImaginary conjugate (linear pair.1, linear pair.2) = linear (complexPairImaginary conjugate pair) := by
  change (-Complex.I / 2 : ℂ) • (linear pair.1 - conjugate (linear pair.2)) =
    linear ((-Complex.I / 2 : ℂ) • (pair.1 - conjugate pair.2))
  rw [commutes, complexLinear, map_sub]

theorem complexPairExtension_linear_relabel (conjugate linear : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) vector, conjugate (scalar • vector) = star scalar • conjugate vector)
    (complexLinear : ∀ (scalar : ℂ) vector, linear (scalar • vector) = scalar • linear vector)
    (commutes : ∀ vector, conjugate (linear vector) = linear (conjugate vector))
    (source target : Space →L[ℝ] Space) (intertwines : ∀ vector, target (linear vector) = linear (source vector))
    (pair : Space × Space) :
    complexPairExtension conjugate antilinear target (linear pair.1, linear pair.2) =
      (linear (complexPairExtension conjugate antilinear source pair).1,
        linear (complexPairExtension conjugate antilinear source pair).2) := by
  change complexPairEmbedding conjugate (target (complexPairReal conjugate (linear pair.1, linear pair.2))) +
      Complex.I • complexPairEmbedding conjugate (target (complexPairImaginary conjugate (linear pair.1, linear pair.2))) =
    (linear (complexPairEmbedding conjugate (source (complexPairReal conjugate pair)) +
      Complex.I • complexPairEmbedding conjugate (source (complexPairImaginary conjugate pair))).1,
     linear (complexPairEmbedding conjugate (source (complexPairReal conjugate pair)) +
      Complex.I • complexPairEmbedding conjugate (source (complexPairImaginary conjugate pair))).2)
  rw [complexPairReal_linear_relabel conjugate linear complexLinear commutes,
    complexPairImaginary_linear_relabel conjugate linear complexLinear commutes,
    intertwines, intertwines]
  apply Prod.ext
  · change linear _ + Complex.I • linear _ = linear (_ + Complex.I • _)
    rw [map_add, complexLinear] <;> rfl
  · change conjugate (linear _) + Complex.I • conjugate (linear _) = linear (_ + Complex.I • _)
    rw [commutes, commutes, map_add, complexLinear] <;> rfl

theorem complexPairPositiveExtension_linear_relabel (conjugate linear : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) vector, conjugate (scalar • vector) = star scalar • conjugate vector)
    (complexLinear : ∀ (scalar : ℂ) vector, linear (scalar • vector) = scalar • linear vector)
    (commutes : ∀ vector, conjugate (linear vector) = linear (conjugate vector))
    (source target : Space →L[ℝ] Space) (intertwines : ∀ vector, target (linear vector) = linear (source vector))
    (pair : Space × Space) :
    complexPairPositiveExtension conjugate antilinear target (linear pair.1, linear pair.2) =
      (linear (complexPairPositiveExtension conjugate antilinear source pair).1,
        linear (complexPairPositiveExtension conjugate antilinear source pair).2) := by
  have imaginaryIntertwines (vector : Space) :
      (Complex.I • target) (linear vector) = linear ((Complex.I • source) vector) := by
    simp only [ContinuousLinearMap.smul_apply]
    rw [intertwines, complexLinear]
  have first := complexPairExtension_linear_relabel conjugate linear antilinear complexLinear commutes
    source target intertwines pair
  have second := complexPairExtension_linear_relabel conjugate linear antilinear complexLinear commutes
    (Complex.I • source) (Complex.I • target) imaginaryIntertwines pair
  change (1 / 2 : ℂ) •
      (complexPairExtension conjugate antilinear target (linear pair.1, linear pair.2) -
        Complex.I • complexPairExtension conjugate antilinear (Complex.I • target) (linear pair.1, linear pair.2)) = _
  rw [first, second]
  apply Prod.ext
  · change (1 / 2 : ℂ) • (linear _ - Complex.I • linear _) = linear ((1 / 2 : ℂ) • (_ - Complex.I • _))
    rw [complexLinear, map_sub, complexLinear] <;> rfl
  · change (1 / 2 : ℂ) • (linear _ - Complex.I • linear _) = linear ((1 / 2 : ℂ) • (_ - Complex.I • _))
    rw [complexLinear, map_sub, complexLinear] <;> rfl

theorem complexPairBilinearExtension_linear_relabel (conjugate linear : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) vector, conjugate (scalar • vector) = star scalar • conjugate vector)
    (complexLinear : ∀ (scalar : ℂ) vector, linear (scalar • vector) = scalar • linear vector)
    (commutes : ∀ vector, conjugate (linear vector) = linear (conjugate vector))
    (source target : Space →L[ℝ] Space →L[ℝ] Space)
    (intertwines : ∀ first second, target (linear first) (linear second) = linear (source first second))
    (first second : Space × Space) :
    complexPairBilinearExtension conjugate antilinear target
        (linear first.1, linear first.2) (linear second.1, linear second.2) =
      (linear (complexPairBilinearExtension conjugate antilinear source first second).1,
        linear (complexPairBilinearExtension conjugate antilinear source first second).2) := by
  change complexPairBilinearRealExtension conjugate target
    (linear first.1, linear first.2) (linear second.1, linear second.2) =
    (linear (complexPairBilinearRealExtension conjugate source first second).1,
      linear (complexPairBilinearRealExtension conjugate source first second).2)
  rw [complexPairBilinearRealExtension_apply, complexPairBilinearRealExtension_apply]
  simp only [complexPairReal_linear_relabel conjugate linear complexLinear commutes,
    complexPairImaginary_linear_relabel conjugate linear complexLinear commutes, intertwines]
  apply Prod.ext
  · change linear _ - linear _ + Complex.I • (linear _ + linear _) = linear (_ - _ + Complex.I • (_ + _))
    rw [map_add, map_sub, complexLinear, map_add] <;> rfl
  · change conjugate (linear _) - conjugate (linear _) +
      Complex.I • (conjugate (linear _) + conjugate (linear _)) = linear (_ - _ + Complex.I • (_ + _))
    rw [commutes, commutes, commutes, commutes, map_add, map_sub, complexLinear, map_add] <;> rfl

end EulerNonuniqueness.General
