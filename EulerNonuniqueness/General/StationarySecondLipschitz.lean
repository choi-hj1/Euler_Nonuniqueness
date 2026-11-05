import EulerNonuniqueness.General.SpectralTubularStationarySecond

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

local instance stationarySecondOperatorGroup : NormedAddCommGroup (Space →L[ℝ] Space) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := Space) (F := Space) (σ₁₂ := RingHom.id ℝ)
local instance stationarySecondOperatorSpace : NormedSpace ℝ (Space →L[ℝ] Space) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := Space) (F := Space) (σ₁₂ := RingHom.id ℝ)
local instance stationarySecondBilinearGroup : NormedAddCommGroup (Space →L[ℝ] Space →L[ℝ] Space) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := Space) (F := Space →L[ℝ] Space) (σ₁₂ := RingHom.id ℝ)
local instance stationarySecondBilinearSpace : NormedSpace ℝ (Space →L[ℝ] Space →L[ℝ] Space) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := Space) (F := Space →L[ℝ] Space) (σ₁₂ := RingHom.id ℝ)

theorem spectralTubularStationarySecond_lipschitzNear
    (projection : Space →L[ℝ] Space) (operator : Space → Space →L[ℝ] Space) (point : Space)
    (derivativeLip : LipschitzNear (fderiv ℝ operator) point) :
    LipschitzNear (spectralTubularStationarySecond projection operator) point := by
  let flipOperator : (Space →L[ℝ] Space →L[ℝ] Space) →L[ℝ] Space →L[ℝ] Space →L[ℝ] Space :=
    (ContinuousLinearMap.flipₗᵢ ℝ Space Space Space).toContinuousLinearEquiv.toContinuousLinearMap
  let rightComposition : (Space →L[ℝ] Space →L[ℝ] Space) →L[ℝ]
      Space →L[ℝ] Space →L[ℝ] Space :=
    (ContinuousLinearMap.compL ℝ Space Space (Space →L[ℝ] Space)).flip
      (ContinuousLinearMap.id ℝ Space - projection)
  let transform : (Space →L[ℝ] Space →L[ℝ] Space) →L[ℝ]
      Space →L[ℝ] Space →L[ℝ] Space :=
    ContinuousLinearMap.id ℝ (Space →L[ℝ] Space →L[ℝ] Space) + rightComposition.comp flipOperator
  have imageLip : LipschitzNear transform (fderiv ℝ operator point) :=
    ⟨‖transform‖₊, Set.univ, Filter.univ_mem, transform.lipschitz.lipschitzOnWith⟩
  exact imageLip.comp derivativeLip

end EulerNonuniqueness.General
