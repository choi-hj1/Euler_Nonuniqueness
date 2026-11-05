import EulerNonuniqueness.General.BilinearFiberLipschitz

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem bilinearFiberCoefficientMap_contDiff_order (order : WithTop ℕ∞) :
    ContDiff ℝ order (bilinearFiberCoefficientMap (Space := Space)) := by
  let Domain := ((Space →L[ℝ] Space) × (Space →L[ℝ] Space)) × BilinearEnd Space
  have coordinates : ContDiff ℝ order (fun data : Domain => data.1.2) := contDiff_fst.snd
  have second : ContDiff ℝ order (fun data : Domain => data.2) := contDiff_snd
  have flipSmooth : ContDiff ℝ order (fun bilinear : BilinearEnd Space => bilinear.flip) := by
    have identity : (fun bilinear : BilinearEnd Space => bilinear.flip) =
        (bilinearFlipOperator (Space := Space) : BilinearEnd Space → BilinearEnd Space) := by
      funext bilinear
      rfl
    rw [identity]
    with_reducible
      exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := BilinearEnd Space) (F := BilinearEnd Space)
        (n := order) (bilinearFlipOperator (Space := Space))
  have firstComp : ContDiff ℝ order (fun data : Domain => data.2.comp data.1.2) := second.clm_comp coordinates
  have firstFlip : ContDiff ℝ order (fun data : Domain => (data.2.comp data.1.2).flip) := flipSmooth.comp firstComp
  have secondComp : ContDiff ℝ order (fun data : Domain => (data.2.comp data.1.2).flip.comp data.1.2) :=
    firstFlip.clm_comp coordinates
  have secondFlip : ContDiff ℝ order (fun data : Domain => ((data.2.comp data.1.2).flip.comp data.1.2).flip) :=
    flipSmooth.comp secondComp
  have liftSmooth : ContDiff ℝ order (ContinuousLinearMap.compL ℝ Space Space Space) := by
    with_reducible exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := order) _
  have inverseLift : ContDiff ℝ order (fun data : Domain => ContinuousLinearMap.compL ℝ Space Space Space data.1.1) := by
    simpa only [Function.comp_def] using liftSmooth.comp
      (show ContDiff ℝ order (fun data : Domain => data.1.1) from contDiff_fst.fst)
  exact (inverseLift.clm_comp secondFlip).const_smul (1 / 2 : ℝ)

theorem hasLipschitzDerivativeNear_bilinear_fiber_coefficient
    (coordinates inverse : Space → Space →L[ℝ] Space)
    (second coefficient : Space → BilinearEnd Space)
    (coordinateRegular : HasLipschitzDerivativeNear coordinates (0 : Space))
    (inverseRegular : HasLipschitzDerivativeNear inverse (0 : Space))
    (secondRegular : HasLipschitzDerivativeNear second (0 : Space))
    (identity : ∀ parameter first right,
      coefficient parameter first right = inverse parameter
        ((1 / 2 : ℝ) • second parameter (coordinates parameter first) (coordinates parameter right))) :
    HasLipschitzDerivativeNear coefficient (0 : Space) := by
  have inputRegular := (inverseRegular.prodMk coordinateRegular).prodMk secondRegular
  have mapRegular : HasLipschitzDerivativeNear (bilinearFiberCoefficientMap (Space := Space))
      ((inverse 0, coordinates 0), second 0) :=
    hasLipschitzDerivativeNear_of_contDiffAt_two (bilinearFiberCoefficientMap_contDiff_order 2).contDiffAt
  have regular : HasLipschitzDerivativeNear (fun parameter =>
      bilinearFiberCoefficientMap ((inverse parameter, coordinates parameter), second parameter)) (0 : Space) :=
    HasLipschitzDerivativeNear.comp (outer := bilinearFiberCoefficientMap (Space := Space))
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

end

end EulerNonuniqueness.General
