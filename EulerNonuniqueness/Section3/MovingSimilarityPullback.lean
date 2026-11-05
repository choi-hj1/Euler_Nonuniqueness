import EulerNonuniqueness.Section3.SimilarityPatchGreen
import EulerNonuniqueness.Section3.NearCircleSpacetimeReynolds

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

def movingSimilarityMap (center : ℝ → ℂ) (phase : ℝ → ℝ) (radius : ℝ) (point : ℝ × ℂ) : ℝ × ℂ :=
  (point.1, center point.1 + radius • ((Circle.exp (phase point.1) : ℂ) * point.2))

def movingSimilarityDerivative (centerVelocity : ℝ → ℂ) (phase phaseVelocity : ℝ → ℝ)
    (radius : ℝ) (point : ℝ × ℂ) : (ℝ × ℂ) →L[ℝ] (ℝ × ℂ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℂ).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
      (centerVelocity point.1 + radius •
        ((Complex.I * (phaseVelocity point.1 : ℂ)) * (Circle.exp (phase point.1) : ℂ) * point.2)) +
      radius • ((Circle.exp (phase point.1) : ℂ) • ContinuousLinearMap.snd ℝ ℝ ℂ))

theorem hasDerivAt_circle_phase {phase : ℝ → ℝ} {phaseVelocity time : ℝ}
    (equation : HasDerivAt phase phaseVelocity time) :
    HasDerivAt (fun parameter => (Circle.exp (phase parameter) : ℂ))
      ((Complex.I * (phaseVelocity : ℂ)) * (Circle.exp (phase time) : ℂ)) time := by
  have derivative := (equation.ofReal_comp.mul_const Complex.I).cexp
  simpa only [Circle.coe_exp, mul_comm, mul_left_comm, mul_assoc] using derivative

theorem hasFDerivAt_movingSimilarityMap
    (center centerVelocity : ℝ → ℂ) (phase phaseVelocity : ℝ → ℝ) (radius : ℝ)
    (centerEquation : ∀ time, HasDerivAt center (centerVelocity time) time)
    (phaseEquation : ∀ time, HasDerivAt phase (phaseVelocity time) time) (point : ℝ × ℂ) :
    HasFDerivAt (movingSimilarityMap center phase radius)
      (movingSimilarityDerivative centerVelocity phase phaseVelocity radius point) point := by
  have centerDerivative := (centerEquation point.1).hasFDerivAt.comp point
    (ContinuousLinearMap.fst ℝ ℝ ℂ).hasFDerivAt
  have phaseDerivative := (hasDerivAt_circle_phase (phaseEquation point.1)).hasFDerivAt.comp point
    (ContinuousLinearMap.fst ℝ ℝ ℂ).hasFDerivAt
  have spatialDerivative := centerDerivative.add
    ((phaseDerivative.mul (ContinuousLinearMap.snd ℝ ℝ ℂ).hasFDerivAt).const_smul radius)
  apply ((ContinuousLinearMap.fst ℝ ℝ ℂ).hasFDerivAt.prodMk spatialDerivative).congr_fderiv
  apply ContinuousLinearMap.ext
  intro direction
  apply Prod.ext
  · rfl
  · simp [movingSimilarityDerivative, ContinuousLinearMap.prod_apply, Complex.real_smul, Function.comp_def]
    ring

theorem continuous_movingSimilarityMap (center : ℝ → ℂ) (phase : ℝ → ℝ) (radius : ℝ)
    (centerContinuous : Continuous center) (phaseContinuous : Continuous phase) :
    Continuous (movingSimilarityMap center phase radius) := by
  unfold movingSimilarityMap
  apply continuous_fst.prodMk
  exact (centerContinuous.comp continuous_fst).add
    (continuous_const.smul (((continuous_subtype_val.comp (Circle.exp.continuous.comp phaseContinuous)).comp continuous_fst).mul continuous_snd))

theorem continuous_movingSimilarityDerivative (centerVelocity : ℝ → ℂ) (phase phaseVelocity : ℝ → ℝ)
    (radius : ℝ) (centerVelocityContinuous : Continuous centerVelocity)
    (phaseContinuous : Continuous phase) (phaseVelocityContinuous : Continuous phaseVelocity) :
    Continuous (movingSimilarityDerivative centerVelocity phase phaseVelocity radius) := by
  have rotationContinuous : Continuous (fun point : ℝ × ℂ => (Circle.exp (phase point.1) : ℂ)) :=
    (continuous_subtype_val.comp (Circle.exp.continuous.comp phaseContinuous)).comp continuous_fst
  have driftContinuous : Continuous (fun point : ℝ × ℂ => centerVelocity point.1 + radius •
      ((Complex.I * (phaseVelocity point.1 : ℂ)) * (Circle.exp (phase point.1) : ℂ) * point.2)) := by
    exact (centerVelocityContinuous.comp continuous_fst).add (continuous_const.smul
      (((continuous_const.mul (Complex.continuous_ofReal.comp (phaseVelocityContinuous.comp continuous_fst))).mul
        rotationContinuous).mul continuous_snd))
  have scalarPart : Continuous (fun point : ℝ × ℂ => (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
      (centerVelocity point.1 + radius •
        ((Complex.I * (phaseVelocity point.1 : ℂ)) * (Circle.exp (phase point.1) : ℂ) * point.2))) :=
    Continuous.clm_apply
      ((ContinuousLinearMap.smulRightL ℝ (ℝ × ℂ) ℂ).continuous.comp continuous_const) driftContinuous
  have spatialContinuous : Continuous (fun point : ℝ × ℂ =>
      (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
        (centerVelocity point.1 + radius •
          ((Complex.I * (phaseVelocity point.1 : ℂ)) * (Circle.exp (phase point.1) : ℂ) * point.2)) +
        radius • ((Circle.exp (phase point.1) : ℂ) • ContinuousLinearMap.snd ℝ ℝ ℂ)) :=
    scalarPart.add (continuous_const.smul (rotationContinuous.smul continuous_const))
  have combined : Continuous (fun point : ℝ × ℂ =>
      (ContinuousLinearMap.inl ℝ ℝ ℂ).comp (ContinuousLinearMap.fst ℝ ℝ ℂ) +
        (ContinuousLinearMap.inr ℝ ℝ ℂ).comp
          ((ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
            (centerVelocity point.1 + radius •
              ((Complex.I * (phaseVelocity point.1 : ℂ)) * (Circle.exp (phase point.1) : ℂ) * point.2)) +
            radius • ((Circle.exp (phase point.1) : ℂ) • ContinuousLinearMap.snd ℝ ℝ ℂ))) :=
    continuous_const.add (continuous_const.clm_comp spatialContinuous)
  apply combined.congr
  intro point
  apply ContinuousLinearMap.ext
  intro direction
  simp [movingSimilarityDerivative]

theorem movingSimilarityDerivative_temporal (centerVelocity : ℝ → ℂ) (phase phaseVelocity : ℝ → ℝ)
    (radius : ℝ) (point : ℝ × ℂ) :
    movingSimilarityDerivative centerVelocity phase phaseVelocity radius point (1, 0) =
      (1, centerVelocity point.1 + radius •
        ((Complex.I * (phaseVelocity point.1 : ℂ)) * (Circle.exp (phase point.1) : ℂ) * point.2)) := by
  simp [movingSimilarityDerivative]

end EulerNonuniqueness.Paper
