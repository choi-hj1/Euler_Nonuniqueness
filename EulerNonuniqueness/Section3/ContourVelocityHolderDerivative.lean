import EulerNonuniqueness.Section3.ContourCauchyJointDerivative
import EulerNonuniqueness.Section3.ContourVelocityCauchyRepresentation

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance velocityHolderDerivativeRealSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance velocityC1DerivativeRealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

local instance velocityHolderOperatorGroup : SeminormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance velocityHolderOperatorComplexSpace : NormedSpace ℂ (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)

def c1ValueHolderRealCLM : PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf :=
  LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf)
    ({ toFun := fun data : PeriodicC1HolderHalf => c1ValueHolder data
       map_add' := fun first second => by
         apply PeriodicHolderHalf.ext_value
         intro label
         rfl
       map_smul' := fun scalar data => by
         apply PeriodicHolderHalf.ext_value
         intro label
         rfl } : PeriodicC1HolderHalf →ₗ[ℝ] PeriodicHolderHalf)
    2 c1ValueHolder_norm_bound

def contourHolderConjugateRealCLM : PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf :=
  LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicHolderHalf) (F := PeriodicHolderHalf)
    ({ toFun := fun data : PeriodicHolderHalf => holderConjugate data
       map_add' := fun first second => by
         apply PeriodicHolderHalf.ext_value
         intro label
         exact star_add _ _
       map_smul' := fun scalar data => by
         apply PeriodicHolderHalf.ext_value
         intro label
         exact star_smul scalar (data.val.1 label) } : PeriodicHolderHalf →ₗ[ℝ] PeriodicHolderHalf)
    1 (fun data => by simpa only [one_mul] using holderConjugate_norm_bound data)

def contourVelocityHolderDerivativeCLM (data : PeriodicC1HolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) : PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf :=
  (Complex.I / 4) • c1ValueHolderRealCLM - (1 / (4 * Real.pi) : ℂ) •
    contourHolderConjugateRealCLM.comp
      ((contourCauchyJointDerivativeCLM data (holderConjugate (c1ValueHolder data)) near small).comp
        ((ContinuousLinearMap.id ℝ PeriodicC1HolderHalf).prod
          (contourHolderConjugateRealCLM.comp c1ValueHolderRealCLM)))

theorem hasFDerivAt_holderContourVelocity (data : PeriodicC1HolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    HasFDerivAt holderContourVelocity (contourVelocityHolderDerivativeCLM data near small) data := by
  let pairMap : PeriodicC1HolderHalf →L[ℝ] (PeriodicC1HolderHalf × PeriodicHolderHalf) :=
    (ContinuousLinearMap.id ℝ PeriodicC1HolderHalf).prod
    (contourHolderConjugateRealCLM.comp c1ValueHolderRealCLM)
  have pair : HasFDerivAt
      (fun current : PeriodicC1HolderHalf => (current, holderConjugate (c1ValueHolder current))) pairMap data := by
    change HasFDerivAt (fun current : PeriodicC1HolderHalf => pairMap current) pairMap data
    exact ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf × PeriodicHolderHalf) pairMap
  have outer : HasFDerivAt
      (fun pair : PeriodicC1HolderHalf × PeriodicHolderHalf => extendedContourCauchy pair.1 pair.2)
      (contourCauchyJointDerivativeCLM data (holderConjugate (c1ValueHolder data)) near small)
      (data, holderConjugate (c1ValueHolder data)) := by
    exact hasFDerivAt_contourCauchy_joint data (holderConjugate (c1ValueHolder data)) near small
  have cauchy : HasFDerivAt
      (fun current : PeriodicC1HolderHalf => extendedContourCauchy current (holderConjugate (c1ValueHolder current)))
      ((contourCauchyJointDerivativeCLM data (holderConjugate (c1ValueHolder data)) near small).comp pairMap) data := by
    exact
    HasFDerivAt.comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf × PeriodicHolderHalf) (G := PeriodicHolderHalf)
      (f := fun current : PeriodicC1HolderHalf => (current, holderConjugate (c1ValueHolder current)))
      (f' := pairMap)
      (g := fun pair : PeriodicC1HolderHalf × PeriodicHolderHalf => extendedContourCauchy pair.1 pair.2)
      (g' := contourCauchyJointDerivativeCLM data (holderConjugate (c1ValueHolder data)) near small) data
      outer pair
  have conjugated : HasFDerivAt
      (fun current : PeriodicC1HolderHalf => holderConjugate
        (extendedContourCauchy current (holderConjugate (c1ValueHolder current))))
      (contourHolderConjugateRealCLM.comp
        ((contourCauchyJointDerivativeCLM data (holderConjugate (c1ValueHolder data)) near small).comp pairMap)) data :=
    contourHolderConjugateRealCLM.hasFDerivAt.comp data cauchy
  have left : HasFDerivAt (fun current : PeriodicC1HolderHalf => (Complex.I / 4) • c1ValueHolder current)
      ((Complex.I / 4) • c1ValueHolderRealCLM) data := by
    exact (c1ValueHolderRealCLM.hasFDerivAt (x := data)).const_smul (Complex.I / 4)
  have right : HasFDerivAt
      (fun current : PeriodicC1HolderHalf => (1 / (4 * Real.pi) : ℂ) • holderConjugate
        (extendedContourCauchy current (holderConjugate (c1ValueHolder current))))
      ((1 / (4 * Real.pi) : ℂ) • contourHolderConjugateRealCLM.comp
        ((contourCauchyJointDerivativeCLM data (holderConjugate (c1ValueHolder data)) near small).comp pairMap)) data := by
    exact HasFDerivAt.const_smul (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf)
      (R := ℂ) conjugated (1 / (4 * Real.pi) : ℂ)
  exact HasFDerivAt.sub (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) left right

end

end EulerNonuniqueness.Paper
