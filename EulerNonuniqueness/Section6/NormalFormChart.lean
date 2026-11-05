import EulerNonuniqueness.Section6.NormalFormRemainder

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

def localNormalFormChart (graph coordinate : ℝ → ℝ) (point : ℝ × ℝ) : ℝ × ℝ :=
  (coordinate point.1, point.2 - graph point.1)

theorem localNormalFormChart_regular {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ContDiffAt ℝ 2 (localNormalFormChart graph coordinate) 0 ∧
      localNormalFormChart graph coordinate 0 = 0 ∧
      HasFDerivAt (localNormalFormChart graph coordinate) (ContinuousLinearMap.id ℝ (ℝ × ℝ)) 0 := by
  have coordinateFDeriv : HasFDerivAt coordinate (ContinuousLinearMap.id ℝ ℝ) 0 := by
    convert coordinateDerivative.hasFDerivAt using 1
    apply ContinuousLinearMap.ext
    intro point
    simp
  have graphFDeriv : HasFDerivAt graph (0 : ℝ →L[ℝ] ℝ) 0 := by
    convert graphDerivative.hasFDerivAt using 1
    apply ContinuousLinearMap.ext
    intro point
    simp
  have first := coordinateFDeriv.comp (0 : ℝ × ℝ) (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ)))
  have second := (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ))).sub
    (graphFDeriv.comp (0 : ℝ × ℝ) (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ))))
  refine ⟨(ContDiffAt.comp (f := Prod.fst) (g := coordinate) 0 coordinateSmooth contDiffAt_fst).prodMk
    (contDiffAt_snd.sub (ContDiffAt.comp (f := Prod.fst) (g := graph) 0 graphSmooth contDiffAt_fst)), ?_, ?_⟩
  · simp [localNormalFormChart, graphZero, coordinateZero]
  · convert first.prodMk second using 1
    apply ContinuousLinearMap.ext
    intro point
    simp

theorem localNormalFormChart_local_inverse {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ inverse : (ℝ × ℝ) → ℝ × ℝ, ContDiffAt ℝ 2 inverse 0 ∧ inverse 0 = 0 ∧
      (∀ᶠ point in nhds (0 : ℝ × ℝ), inverse (localNormalFormChart graph coordinate point) = point) ∧
      (∀ᶠ point in nhds (0 : ℝ × ℝ), localNormalFormChart graph coordinate (inverse point) = point) := by
  have regular := localNormalFormChart_regular graphSmooth coordinateSmooth graphZero coordinateZero
    graphDerivative coordinateDerivative
  have derivative : HasFDerivAt (localNormalFormChart graph coordinate)
      (ContinuousLinearEquiv.refl ℝ (ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) 0 := regular.2.2
  let inverse := regular.1.localInverse derivative (by norm_num)
  have inverseZero : inverse 0 = 0 := by
    simpa only [regular.2.1] using regular.1.localInverse_apply_image derivative (by norm_num)
  have inverseSmooth : ContDiffAt ℝ 2 inverse 0 := by
    simpa only [regular.2.1] using regular.1.to_localInverse derivative (by norm_num)
  have strict := regular.1.hasStrictFDerivAt' derivative (by norm_num)
  refine ⟨inverse, inverseSmooth, inverseZero, strict.eventually_left_inverse, ?_⟩
  simpa only [regular.2.1] using strict.eventually_right_inverse

theorem localNormalFormChart_forced_equation {graph coordinate : ℝ → ℝ}
    {trajectory : ℝ → ℝ × ℝ} {frequency time : ℝ} {forcing : ℝ × ℝ}
    (equation : HasDerivAt trajectory (shapeChartVelocity frequency (trajectory time) + forcing) time)
    (graphDifferentiable : DifferentiableAt ℝ graph (trajectory time).1)
    (coordinateDifferentiable : DifferentiableAt ℝ coordinate (trajectory time).1) :
    HasDerivAt (fun currentTime => localNormalFormChart graph coordinate (trajectory currentTime))
      (2 * Real.sqrt 2 * frequency * (localNormalFormChart graph coordinate (trajectory time)).1 +
          (localNormalFormError frequency graph coordinate (trajectory time)).1 +
          deriv coordinate (trajectory time).1 * forcing.1,
        -(2 * Real.sqrt 2 * frequency) * (localNormalFormChart graph coordinate (trajectory time)).2 +
          (localNormalFormError frequency graph coordinate (trajectory time)).2 + forcing.2 -
          deriv graph (trajectory time).1 * forcing.1) time := by
  have firstComponent : HasDerivAt (fun currentTime => (trajectory currentTime).1)
      ((shapeChartVelocity frequency (trajectory time)).1 + forcing.1) time :=
    HasFDerivAt.comp_hasDerivAt (l := Prod.fst) (l' := ContinuousLinearMap.fst ℝ ℝ ℝ)
      time (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt equation
  have secondComponent : HasDerivAt (fun currentTime => (trajectory currentTime).2)
      ((shapeChartVelocity frequency (trajectory time)).2 + forcing.2) time :=
    HasFDerivAt.comp_hasDerivAt (l := Prod.snd) (l' := ContinuousLinearMap.snd ℝ ℝ ℝ)
      time (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt equation
  have first := coordinateDifferentiable.hasDerivAt.comp time firstComponent
  have second := secondComponent.sub (graphDifferentiable.hasDerivAt.comp time firstComponent)
  have combined : HasDerivAt (fun currentTime => localNormalFormChart graph coordinate (trajectory currentTime))
      (deriv coordinate (trajectory time).1 * ((shapeChartVelocity frequency (trajectory time)).1 + forcing.1),
        (shapeChartVelocity frequency (trajectory time)).2 + forcing.2 -
          deriv graph (trajectory time).1 * ((shapeChartVelocity frequency (trajectory time)).1 + forcing.1)) time :=
    first.prodMk second
  convert combined using 1 <;> dsimp [localNormalFormChart, localNormalFormError] <;> ring

end EulerNonuniqueness.Section6
