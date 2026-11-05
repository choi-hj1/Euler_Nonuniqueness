import EulerNonuniqueness.General.ComplexCubicSolverRealRegularity
import EulerNonuniqueness.General.ForcingNumeratorRealRegularity
import EulerNonuniqueness.Section3.LocalDerivativeLipschitzCalculus

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℂ Space]

theorem complexCubicProjection_contDiff_order (branch : Fin 3) (order : WithTop ℕ∞) :
    ContDiff ℂ order (fun operator : Space →L[ℂ] Space => complexCubicProjection operator branch) := by
  have square : ContDiff ℂ order (fun operator : Space →L[ℂ] Space => operator.comp operator) :=
    contDiff_id.clm_comp contDiff_id
  fin_cases branch
  · change ContDiff ℂ order (fun operator : Space →L[ℂ] Space =>
      ContinuousLinearMap.id ℂ Space + (4 : ℂ) • operator.comp operator)
    exact contDiff_const.add (square.const_smul (4 : ℂ))
  · change ContDiff ℂ order (fun operator : Space →L[ℂ] Space =>
      (-2 : ℂ) • operator.comp operator - Complex.I • operator)
    exact (square.const_smul (-2 : ℂ)).sub (contDiff_id.const_smul Complex.I)
  · change ContDiff ℂ order (fun operator : Space →L[ℂ] Space =>
      (-2 : ℂ) • operator.comp operator + Complex.I • operator)
    exact (square.const_smul (-2 : ℂ)).add (contDiff_id.const_smul Complex.I)

theorem complexCubicHomologicalSolver_contDiff_order
    (eigenvalue : Fin 3 → ℂ) (frequency : ℂ) (order : WithTop ℕ∞) :
    ContDiff ℂ order (fun data : (Space →L[ℂ] Space) × (Space →L[ℂ] Space) =>
      finiteSpectralHomologicalSolver (complexCubicProjection data.1) eigenvalue frequency data.2) := by
  have projections (branch : Fin 3) : ContDiff ℂ order
      (fun data : (Space →L[ℂ] Space) × (Space →L[ℂ] Space) => complexCubicProjection data.1 branch) :=
    (complexCubicProjection_contDiff_order branch order).comp contDiff_fst
  unfold finiteSpectralHomologicalSolver
  apply ContDiff.sum
  intro output _
  apply ContDiff.sum
  intro input _
  exact ((projections output).clm_comp (contDiff_snd.clm_comp (projections input))).const_smul
    ((frequency + eigenvalue input - eigenvalue output)⁻¹)

attribute [local instance] numeratorOperatorGroup numeratorOperatorSpace numeratorBilinearGroup numeratorBilinearSpace

theorem forcingLinearCoefficient_contDiff_order (order : WithTop ℕ∞) :
    ContDiff ℂ order
      (fun data : (Space →L[ℂ] Space) × ((Space →L[ℂ] Space →L[ℂ] Space) × Space) =>
        forcingLinearCoefficient data.1 data.2.1 data.2.2) := by
  let flipMap : (Space →L[ℂ] Space →L[ℂ] Space) →L[ℂ] Space →L[ℂ] Space →L[ℂ] Space :=
    (ContinuousLinearMap.flipₗᵢ ℂ Space Space Space).toContinuousLinearEquiv.toContinuousLinearMap
  have flipSmooth : ContDiff ℂ order flipMap := by
    with_reducible_and_instances
      exact ContinuousLinearMap.contDiff (𝕜 := ℂ)
        (E := Space →L[ℂ] Space →L[ℂ] Space) (F := Space →L[ℂ] Space →L[ℂ] Space) (n := order) flipMap
  have componentSmooth : ContDiff ℂ order
      (fun data : (Space →L[ℂ] Space) × ((Space →L[ℂ] Space →L[ℂ] Space) × Space) => data.2.1) :=
    contDiff_fst.comp contDiff_snd
  have flipped : ContDiff ℂ order
      (fun data : (Space →L[ℂ] Space) × ((Space →L[ℂ] Space →L[ℂ] Space) × Space) => flipMap data.2.1) :=
    flipSmooth.comp componentSmooth
  exact contDiff_fst.add ((flipped.clm_apply (contDiff_snd.comp contDiff_snd)).const_smul (2 : ℂ))

variable [NormedSpace ℝ Space] [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]

attribute [local instance] numeratorOperatorGroup numeratorOperatorSpace numeratorBilinearGroup numeratorBilinearSpace
  numeratorRealOperatorSpace numeratorRealBilinearSpace numeratorOperatorTower numeratorBilinearTower numeratorTupleTower
  solverRealOperatorSpace solverOperatorTower solverTupleTower

theorem complexCubicHomologicalSolver_hasLipschitzDerivativeNear
    (eigenvalue : Fin 3 → ℂ) (frequency : ℂ)
    (point : (Space →L[ℂ] Space) × (Space →L[ℂ] Space)) :
    HasLipschitzDerivativeNear
      (fun data : (Space →L[ℂ] Space) × (Space →L[ℂ] Space) =>
        finiteSpectralHomologicalSolver (complexCubicProjection data.1) eigenvalue frequency data.2) point := by
  have smooth : ContDiff ℝ 2
      (fun data : (Space →L[ℂ] Space) × (Space →L[ℂ] Space) =>
        finiteSpectralHomologicalSolver (complexCubicProjection data.1) eigenvalue frequency data.2) :=
    (complexCubicHomologicalSolver_contDiff_order eigenvalue frequency 2).restrict_scalars ℝ
  exact hasLipschitzDerivativeNear_of_contDiffAt_two smooth.contDiffAt

theorem forcingLinearCoefficient_hasLipschitzDerivativeNear
    (point : (Space →L[ℂ] Space) × ((Space →L[ℂ] Space →L[ℂ] Space) × Space)) :
    HasLipschitzDerivativeNear
      (fun data : (Space →L[ℂ] Space) × ((Space →L[ℂ] Space →L[ℂ] Space) × Space) =>
        forcingLinearCoefficient data.1 data.2.1 data.2.2) point := by
  have smooth : ContDiff ℝ 2
      (fun data : (Space →L[ℂ] Space) × ((Space →L[ℂ] Space →L[ℂ] Space) × Space) =>
        forcingLinearCoefficient data.1 data.2.1 data.2.2) :=
    (forcingLinearCoefficient_contDiff_order 2).restrict_scalars ℝ
  exact hasLipschitzDerivativeNear_of_contDiffAt_two smooth.contDiffAt

end EulerNonuniqueness.General
