import EulerNonuniqueness.General.QuadraticCommutatorOperator
import EulerNonuniqueness.Section3.LocalDerivativeLipschitzCalculus

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

def bilinearFiberCoefficientMap
    (data : ((Space →L[ℝ] Space) × (Space →L[ℝ] Space)) × BilinearEnd Space) : BilinearEnd Space :=
  (1 / 2 : ℝ) • bilinearPostcompose data.1.1 (data.2.bilinearComp data.1.2 data.1.2)

theorem bilinearFiberCoefficientMap_contDiff :
    ContDiff ℝ 1 (bilinearFiberCoefficientMap (Space := Space)) := by
  let Domain := ((Space →L[ℝ] Space) × (Space →L[ℝ] Space)) × BilinearEnd Space
  have coordinates : ContDiff ℝ 1 (fun data : Domain => data.1.2) := contDiff_fst.snd
  have second : ContDiff ℝ 1 (fun data : Domain => data.2) := contDiff_snd
  have flipSmooth : ContDiff ℝ 1 (fun bilinear : BilinearEnd Space => bilinear.flip) := by
    have identity : (fun bilinear : BilinearEnd Space => bilinear.flip) =
        (bilinearFlipOperator (Space := Space) : BilinearEnd Space → BilinearEnd Space) := by
      funext bilinear
      rfl
    rw [identity]
    with_reducible
      exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := BilinearEnd Space) (F := BilinearEnd Space)
        (n := 1) (bilinearFlipOperator (Space := Space))
  have firstComp : ContDiff ℝ 1 (fun data : Domain => data.2.comp data.1.2) := second.clm_comp coordinates
  have firstFlip : ContDiff ℝ 1 (fun data : Domain => (data.2.comp data.1.2).flip) :=
    flipSmooth.comp firstComp
  have secondComp : ContDiff ℝ 1 (fun data : Domain => (data.2.comp data.1.2).flip.comp data.1.2) :=
    firstFlip.clm_comp coordinates
  have secondFlip : ContDiff ℝ 1 (fun data : Domain => ((data.2.comp data.1.2).flip.comp data.1.2).flip) :=
    flipSmooth.comp secondComp
  have liftSmooth : ContDiff ℝ 1 (ContinuousLinearMap.compL ℝ Space Space Space) := by
    with_reducible exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := 1) _
  have inverseLift : ContDiff ℝ 1 (fun data : Domain => ContinuousLinearMap.compL ℝ Space Space Space data.1.1) := by
    simpa only [Function.comp_def] using liftSmooth.comp (show ContDiff ℝ 1 (fun data : Domain => data.1.1) from contDiff_fst.fst)
  exact (inverseLift.clm_comp secondFlip).const_smul (1 / 2 : ℝ)

theorem lipschitzNear_bilinear_fiber_coefficient
    (coordinates inverse : Space → Space →L[ℝ] Space)
    (second coefficient : Space → BilinearEnd Space)
    (coordinateRegular : LipschitzNear coordinates (0 : Space))
    (inverseRegular : LipschitzNear inverse (0 : Space))
    (secondRegular : LipschitzNear second (0 : Space))
    (identity : ∀ parameter first right,
      coefficient parameter first right = inverse parameter
        ((1 / 2 : ℝ) • second parameter (coordinates parameter first) (coordinates parameter right))) :
    LipschitzNear coefficient (0 : Space) := by
  have inputRegular := (inverseRegular.prodMk coordinateRegular).prodMk secondRegular
  have mapRegular : LipschitzNear (bilinearFiberCoefficientMap (Space := Space))
      ((inverse 0, coordinates 0), second 0) :=
    lipschitzNear_of_contDiffAt_one bilinearFiberCoefficientMap_contDiff.contDiffAt
  have regular : LipschitzNear (fun parameter =>
      bilinearFiberCoefficientMap ((inverse parameter, coordinates parameter), second parameter)) (0 : Space) :=
    LipschitzNear.comp (outer := bilinearFiberCoefficientMap (Space := Space))
      (inner := fun parameter => ((inverse parameter, coordinates parameter), second parameter)) mapRegular inputRegular
  apply regular.congr
  exact Filter.Eventually.of_forall (fun parameter => by
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro right
    rw [identity]
    change inverse parameter ((1 / 2 : ℝ) • second parameter (coordinates parameter first) (coordinates parameter right)) =
      (1 / 2 : ℝ) • inverse parameter (second parameter (coordinates parameter first) (coordinates parameter right))
    exact map_smul _ _ _)

variable [CompleteSpace Space]

theorem hasLipschitzDerivativeNear_inverse_family_of_identity
    (operator : Space → Space →L[ℝ] Space)
    (regular : HasLipschitzDerivativeNear operator (0 : Space))
    (identity : operator 0 = ContinuousLinearMap.id ℝ Space) :
    HasLipschitzDerivativeNear (fun value => Ring.inverse (operator value)) (0 : Space) := by
  have inverseRegular : HasLipschitzDerivativeNear (Ring.inverse : (Space →L[ℝ] Space) → Space →L[ℝ] Space)
      (operator 0) := by
    rw [identity]
    exact hasLipschitzDerivativeNear_of_analyticAt (analyticAt_inverse (𝕜 := ℝ) (1 : (Space →L[ℝ] Space)ˣ))
  exact inverseRegular.comp regular

end

end EulerNonuniqueness.General
