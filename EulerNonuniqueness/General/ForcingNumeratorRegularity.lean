import EulerNonuniqueness.General.WeightedQuadraticLinearCoefficient
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section

namespace EulerNonuniqueness.General

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℂ Space]

local instance numeratorOperatorGroup : NormedAddCommGroup (Space →L[ℂ] Space) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := Space) (F := Space) (σ₁₂ := RingHom.id ℂ)
local instance numeratorOperatorSpace : NormedSpace ℂ (Space →L[ℂ] Space) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ) (E := Space) (F := Space) (σ₁₂ := RingHom.id ℂ)
local instance numeratorBilinearGroup : NormedAddCommGroup (Space →L[ℂ] Space →L[ℂ] Space) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := Space) (F := Space →L[ℂ] Space) (σ₁₂ := RingHom.id ℂ)
local instance numeratorBilinearSpace : NormedSpace ℂ (Space →L[ℂ] Space →L[ℂ] Space) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ) (E := Space) (F := Space →L[ℂ] Space) (σ₁₂ := RingHom.id ℂ)

theorem forcingLinearCoefficient_contDiff :
    ContDiff ℂ 1 (fun data : (Space →L[ℂ] Space) × ((Space →L[ℂ] Space →L[ℂ] Space) × Space) =>
      forcingLinearCoefficient data.1 data.2.1 data.2.2) := by
  let flipMap : (Space →L[ℂ] Space →L[ℂ] Space) →L[ℂ] Space →L[ℂ] Space →L[ℂ] Space :=
    (ContinuousLinearMap.flipₗᵢ ℂ Space Space Space).toContinuousLinearEquiv.toContinuousLinearMap
  have flipSmooth : ContDiff ℂ 1 flipMap :=
    ContinuousLinearMap.contDiff (𝕜 := ℂ) (n := 1) flipMap
  have componentSmooth : ContDiff ℂ 1
      (fun data : (Space →L[ℂ] Space) × ((Space →L[ℂ] Space →L[ℂ] Space) × Space) => data.2.1) :=
    contDiff_fst.comp contDiff_snd
  have flipped : ContDiff ℂ 1
      (fun data : (Space →L[ℂ] Space) × ((Space →L[ℂ] Space →L[ℂ] Space) × Space) => flipMap data.2.1) :=
    flipSmooth.comp componentSmooth
  have applied := flipped.clm_apply (contDiff_snd.comp contDiff_snd)
  exact contDiff_fst.add (applied.const_smul (2 : ℂ))

end EulerNonuniqueness.General
