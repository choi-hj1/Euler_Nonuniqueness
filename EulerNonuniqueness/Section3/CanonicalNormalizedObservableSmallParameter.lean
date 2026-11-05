import EulerNonuniqueness.Section3.CanonicalNormalizedObservableParameter

noncomputable section

open Filter Metric MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace

open EulerNonuniqueness.Section6

theorem canonicalNormalizedQuadraticObservable_exists_uniform_small_parameter_bound :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (first second : PeriodicC1HolderHalf), ‖first‖ ≤ radius → ‖second‖ ≤ radius →
      (∀ label, star (first.val.1 label) = first.val.1 label) →
      (∀ label, star (second.val.1 label) = second.val.1 label) →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      48 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) position) ≤ weight →
      weight / |frequency| ≤ radius →
      ∀ data : PeriodicC1HolderHalf, ‖data - standardCircleBanach‖ ≤ radius →
      ‖family.canonicalNormalizedQuadraticObservable index first frequency time data -
        family.canonicalNormalizedQuadraticObservable index second frequency time data‖ ≤
        constant * (weight / |frequency|) * ‖first - second‖ := by
  obtain ⟨parameterRadius, parameterPositive, parameterConstant, parameterOne, parameters⟩ :=
    canonicalNormalizedQuadraticObservable_exists_uniform_parameter_lipschitz
  let budget := min parameterRadius 1
  have budgetPositive : 0 < budget := lt_min parameterPositive (by norm_num)
  have circle : diskRelabelCurve 0 1 = standardCircleBanach := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rw [diskRelabelCurve_value]
    change Complex.exp ((1 : ℂ) * (Complex.I * 0)) * standardCircle label = standardCircle label
    simp
  have relabelLimit : Tendsto (fun angular : PeriodicC1HolderHalf => diskRelabelCurve angular 1)
      (𝓝 0) (𝓝 standardCircleBanach) := by
    simpa only [circle] using (diskRelabelMap_analyticAt 0).continuousAt.tendsto
  obtain ⟨angularRadius, angularPositive, angularBounds⟩ := Metric.eventually_nhds_iff.mp
    (relabelLimit.eventually (Metric.ball_mem_nhds standardCircleBanach (show 0 < budget / 4 by positivity)))
  let radius := min parameterRadius (min (angularRadius / 2) (budget / 2))
  refine ⟨radius, by dsimp [radius]; positivity, 2 * parameterConstant, by linarith, ?_⟩
  intro count family index first second firstSmall secondSmall firstReal secondReal frequency time distance weight
    nonzero positive weightNonnegative small separated weightBound frequencySmall data dataSmall
  have shapes (angular : PeriodicC1HolderHalf) (angularSmall : ‖angular‖ ≤ radius) :
      ‖diskRelabelCurve angular 1 - standardCircleBanach‖ + ‖data - diskRelabelCurve angular 1‖ ≤ budget := by
    have relabelSmall : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < budget / 4 := by
      have actual := angularBounds (show dist angular (0 : PeriodicC1HolderHalf) < angularRadius by
        rw [dist_zero_right]
        exact (angularSmall.trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt (by linarith))
      simpa only [Metric.mem_ball, dist_eq_norm] using actual
    have shapeIdentity : data - diskRelabelCurve angular 1 =
        (data - standardCircleBanach) - (diskRelabelCurve angular 1 - standardCircleBanach) := by abel
    have triangle := norm_sub_le (data - standardCircleBanach) (diskRelabelCurve angular 1 - standardCircleBanach)
    rw [← shapeIdentity] at triangle
    have dataBound := dataSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have firstShape := shapes first firstSmall
  have secondShape := shapes second secondSmall
  have actual := parameters family index first second
    (firstSmall.trans (min_le_left _ _)) (secondSmall.trans (min_le_left _ _)) firstReal secondReal
    nonzero positive weightNonnegative small separated weightBound (frequencySmall.trans (min_le_left _ _)) data
    (firstShape.trans (min_le_left _ _)) (secondShape.trans (min_le_left _ _))
  have relativeBound : ‖data - diskRelabelCurve second 1‖ ≤ 1 := by
    linarith [norm_nonneg (diskRelabelCurve second 1 - standardCircleBanach), min_le_right parameterRadius (1 : ℝ)]
  have enlarged := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (show 1 + ‖data - diskRelabelCurve second 1‖ ≤ 2 by linarith)
      (show 0 ≤ parameterConstant * (weight / |frequency|) by positivity)) (norm_nonneg (first - second))
  exact actual.trans (by convert enlarged using 1 <;> ring)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
