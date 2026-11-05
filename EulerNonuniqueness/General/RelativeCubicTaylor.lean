import EulerNonuniqueness.General.UniformLipschitzSecondTaylor

open Set Metric
open scoped NNReal

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

local instance relativeCubicBilinearGroup : NormedAddCommGroup (BilinearEnd Space) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Space)
    (F := Space →L[ℝ] Space) (σ₁₂ := RingHom.id ℝ)
local instance relativeCubicBilinearSpace : NormedSpace ℝ (BilinearEnd Space) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := Space)
    (F := Space →L[ℝ] Space) (σ₁₂ := RingHom.id ℝ)
local instance relativeCubicThirdGroup : NormedAddCommGroup (Space →L[ℝ] BilinearEnd Space) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Space)
    (F := BilinearEnd Space) (σ₁₂ := RingHom.id ℝ)
local instance relativeCubicThirdSpace : NormedSpace ℝ (Space →L[ℝ] BilinearEnd Space) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := Space)
    (F := BilinearEnd Space) (σ₁₂ := RingHom.id ℝ)

theorem norm_cubic_taylor_remainder_difference_of_lipschitz_third
    (function : Space → Space) (first : Space → Space →L[ℝ] Space)
    (second : Space → BilinearEnd Space)
    (third : Space → Space →L[ℝ] BilinearEnd Space)
    {radius : ℝ} (constant : ℝ≥0)
    (actualFirst : ∀ value ∈ closedBall (0 : Space) radius,
      HasFDerivAt function (first value) value)
    (actualSecond : ∀ value ∈ closedBall (0 : Space) radius,
      HasFDerivAt first (second value) value)
    (actualThird : ∀ value ∈ closedBall (0 : Space) radius,
      HasFDerivAt second (third value) value)
    (lipschitz : LipschitzOnWith constant third (closedBall (0 : Space) radius))
    (initial final increment : Space)
    (initialInside : ‖initial‖ + ‖increment‖ ≤ radius)
    (finalInside : ‖final‖ + ‖increment‖ ≤ radius)
    (initialQuadratic finalQuadratic : BilinearEnd Space)
    (initialSecond : second initial = initialQuadratic + initialQuadratic.flip)
    (finalSecond : second final = finalQuadratic + finalQuadratic.flip) :
    ‖(function (initial + increment) - function initial - first initial increment -
        initialQuadratic increment increment) -
      (function (final + increment) - function final - first final increment -
        finalQuadratic increment increment)‖ ≤
      (constant : ℝ) * ‖initial - final‖ * ‖increment‖ ^ 3 := by
  have contained (base : Space) (baseInside : ‖base‖ + ‖increment‖ ≤ radius)
      (point : Space) (member : point ∈ closedBall (0 : Space) ‖increment‖) :
      base + point ∈ closedBall (0 : Space) radius := by
    apply mem_closedBall_zero_iff.mpr
    exact (norm_add_le base point).trans
      ((add_le_add_left (mem_closedBall_zero_iff.mp member) ‖base‖).trans baseInside)
  let difference := fun point => function (initial + point) - function (final + point)
  let firstDifference := fun point => first (initial + point) - first (final + point)
  let secondDifference := fun point => second (initial + point) - second (final + point)
  let thirdDifference := fun point => third (initial + point) - third (final + point)
  have firstActual (point : Space) (member : point ∈ closedBall (0 : Space) ‖increment‖) :
      HasFDerivAt difference (firstDifference point) point := by
    have initialTranslation := (hasFDerivAt_id (𝕜 := ℝ) point).const_add initial
    have finalTranslation := (hasFDerivAt_id (𝕜 := ℝ) point).const_add final
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      ((actualFirst _ (contained initial initialInside point member)).comp point initialTranslation).sub
        ((actualFirst _ (contained final finalInside point member)).comp point finalTranslation)
  have secondActual (point : Space) (member : point ∈ closedBall (0 : Space) ‖increment‖) :
      HasFDerivAt firstDifference (secondDifference point) point := by
    have initialTranslation := (hasFDerivAt_id (𝕜 := ℝ) point).const_add initial
    have finalTranslation := (hasFDerivAt_id (𝕜 := ℝ) point).const_add final
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      ((actualSecond _ (contained initial initialInside point member)).comp point initialTranslation).sub
        ((actualSecond _ (contained final finalInside point member)).comp point finalTranslation)
  have thirdActual (point : Space) (member : point ∈ closedBall (0 : Space) ‖increment‖) :
      HasFDerivAt secondDifference (thirdDifference point) point := by
    have initialTranslation := (hasFDerivAt_id (𝕜 := ℝ) point).const_add initial
    have finalTranslation := (hasFDerivAt_id (𝕜 := ℝ) point).const_add final
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      ((actualThird _ (contained initial initialInside point member)).comp point initialTranslation).sub
        ((actualThird _ (contained final finalInside point member)).comp point finalTranslation)
  have thirdBound (point : Space) (member : point ∈ closedBall (0 : Space) ‖increment‖) :
      ‖thirdDifference point‖₊ ≤ constant * ‖initial - final‖₊ := by
    have bound := LipschitzOnWith.norm_sub_le (f := third) lipschitz
      (contained initial initialInside point member) (contained final finalInside point member)
    have equal : (initial + point) - (final + point) = initial - final := by abel
    rw [equal] at bound
    exact_mod_cast bound
  have secondLipschitz := Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun point member => (thirdActual point member).hasFDerivWithinAt) thirdBound
    (convex_closedBall (0 : Space) ‖increment‖)
  have secondIdentity : secondDifference 0 =
      (initialQuadratic - finalQuadratic) + (initialQuadratic - finalQuadratic).flip := by
    apply ContinuousLinearMap.ext
    intro firstDirection
    apply ContinuousLinearMap.ext
    intro secondDirection
    simp only [secondDifference, add_zero, initialSecond, finalSecond,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.flip_apply]
    abel
  have bound := norm_cubic_remainder_of_lipschitz_second difference firstDifference secondDifference
    (constant * ‖initial - final‖₊) firstActual secondActual secondLipschitz
    (0 : Space) increment (by simp) (initialQuadratic - finalQuadratic) secondIdentity
  have equal : difference (0 + increment) - difference 0 - firstDifference 0 increment -
      (initialQuadratic - finalQuadratic) increment increment =
      (function (initial + increment) - function initial - first initial increment -
        initialQuadratic increment increment) -
      (function (final + increment) - function final - first final increment -
        finalQuadratic increment increment) := by
    simp only [difference, firstDifference, zero_add, add_zero, ContinuousLinearMap.sub_apply]
    abel
  simpa only [equal, NNReal.coe_mul, coe_nnnorm] using bound

end

end EulerNonuniqueness.General
