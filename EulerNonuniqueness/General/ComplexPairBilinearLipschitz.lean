import EulerNonuniqueness.General.ComplexPairBilinearBounds
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space]
  [NormedSpace ℂ Space] [NormedSpace ℝ Space]
  [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]

local instance realBilinearOperatorGroup : NormedAddCommGroup (Space →L[ℝ] Space) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Space) (F := Space) (σ₁₂ := RingHom.id ℝ)
local instance realBilinearOperatorSpace : NormedSpace ℝ (Space →L[ℝ] Space) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := Space) (F := Space) (σ₁₂ := RingHom.id ℝ)
local instance realBilinearParameterGroup : NormedAddCommGroup (Space →L[ℝ] Space →L[ℝ] Space) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Space) (F := Space →L[ℝ] Space) (σ₁₂ := RingHom.id ℝ)
local instance complexBilinearOperatorGroup : NormedAddCommGroup ((Space × Space) →L[ℂ] Space × Space) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := Space × Space) (F := Space × Space) (σ₁₂ := RingHom.id ℂ)
local instance complexBilinearOperatorSpace : NormedSpace ℂ ((Space × Space) →L[ℂ] Space × Space) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ) (E := Space × Space) (F := Space × Space) (σ₁₂ := RingHom.id ℂ)
local instance complexBilinearParameterGroup : NormedAddCommGroup
    ((Space × Space) →L[ℂ] (Space × Space) →L[ℂ] Space × Space) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := Space × Space)
    (F := (Space × Space) →L[ℂ] Space × Space) (σ₁₂ := RingHom.id ℂ)

theorem complexPairBilinearExtension_sub (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (first second : Space →L[ℝ] Space →L[ℝ] Space) :
    complexPairBilinearExtension conjugate antilinear first -
        complexPairBilinearExtension conjugate antilinear second =
      complexPairBilinearExtension conjugate antilinear (first - second) := by
  apply ContinuousLinearMap.ext
  intro left
  apply ContinuousLinearMap.ext
  intro right
  change complexPairBilinearRealExtension conjugate first left right -
      complexPairBilinearRealExtension conjugate second left right =
    complexPairBilinearRealExtension conjugate (first - second) left right
  simp only [complexPairBilinearRealExtension_apply, ContinuousLinearMap.sub_apply,
    map_sub, smul_sub, smul_add]
  abel

theorem complexPairBilinearExtension_lipschitz (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector) :
    LipschitzWith (‖complexPairEmbedding conjugate‖₊ *
        (‖complexPairReal conjugate‖₊ + ‖complexPairImaginary conjugate‖₊) ^ 2)
      (complexPairBilinearExtension conjugate antilinear) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  simpa only [dist_eq_norm, complexPairBilinearExtension_sub, NNReal.coe_mul, NNReal.coe_add,
    NNReal.coe_pow, coe_nnnorm] using complexPairBilinearExtension_norm_le conjugate antilinear (first - second)

end EulerNonuniqueness.General
