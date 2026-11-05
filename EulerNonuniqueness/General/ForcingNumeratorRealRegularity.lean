import EulerNonuniqueness.General.ForcingNumeratorRegularity
import EulerNonuniqueness.Section3.LocalLipschitzCalculus

noncomputable section

namespace EulerNonuniqueness.General

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℂ Space] [NormedSpace ℝ Space]
  [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]

attribute [local instance] numeratorOperatorGroup numeratorOperatorSpace numeratorBilinearGroup numeratorBilinearSpace

local instance numeratorRealOperatorSpace : NormedSpace ℝ (Space →L[ℂ] Space) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℝ)
    (E := Space) (F := Space) (σ₁₂ := RingHom.id ℂ)
local instance numeratorRealBilinearSpace : NormedSpace ℝ (Space →L[ℂ] Space →L[ℂ] Space) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℝ)
    (E := Space) (F := Space →L[ℂ] Space) (σ₁₂ := RingHom.id ℂ)
local instance numeratorOperatorTower : IsScalarTower ℝ ℂ (Space →L[ℂ] Space) :=
  ⟨fun scalar coefficient operator => by
    apply ContinuousLinearMap.ext
    intro vector
    exact smul_assoc scalar coefficient (operator vector)⟩
local instance numeratorBilinearTower : IsScalarTower ℝ ℂ (Space →L[ℂ] Space →L[ℂ] Space) :=
  ⟨fun scalar coefficient bilinear => by
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    exact smul_assoc scalar coefficient (bilinear first second)⟩
local instance numeratorTupleTower : IsScalarTower ℝ ℂ
    ((Space →L[ℂ] Space) × ((Space →L[ℂ] Space →L[ℂ] Space) × Space)) :=
  ⟨fun scalar coefficient data => Prod.ext (smul_assoc scalar coefficient data.1)
    (Prod.ext (smul_assoc scalar coefficient data.2.1) (smul_assoc scalar coefficient data.2.2))⟩

theorem forcingLinearCoefficient_real_contDiff :
    ContDiff ℝ 1 (fun data : (Space →L[ℂ] Space) × ((Space →L[ℂ] Space →L[ℂ] Space) × Space) =>
      forcingLinearCoefficient data.1 data.2.1 data.2.2) :=
  (forcingLinearCoefficient_contDiff (Space := Space)).restrict_scalars ℝ

theorem forcingLinearCoefficient_lipschitzNear
    (point : (Space →L[ℂ] Space) × ((Space →L[ℂ] Space →L[ℂ] Space) × Space)) :
    LipschitzNear (fun data : (Space →L[ℂ] Space) × ((Space →L[ℂ] Space →L[ℂ] Space) × Space) =>
      forcingLinearCoefficient data.1 data.2.1 data.2.2) point :=
  lipschitzNear_of_contDiffAt_one (forcingLinearCoefficient_real_contDiff.contDiffAt (x := point))

end EulerNonuniqueness.General
