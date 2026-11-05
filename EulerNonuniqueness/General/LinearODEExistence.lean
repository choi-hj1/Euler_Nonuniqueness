import EulerNonuniqueness.General.ClosedBallProjection
import EulerNonuniqueness.General.BoundedTimeDependentODE
import Mathlib.Analysis.ODE.Gronwall

noncomputable section

open Set Metric
open scoped NNReal Topology

namespace EulerNonuniqueness

theorem exists_linearODE_on_Icc {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [CompleteSpace Space] {coefficient : ℝ → Space →L[ℝ] Space} {horizon : ℝ} (nonnegative : 0 ≤ horizon)
    (continuous : ContinuousOn coefficient (Icc 0 horizon)) {bound : ℝ≥0}
    (bounded : ∀ time ∈ Icc 0 horizon, ‖coefficient time‖ ≤ bound) (initial : Space) :
    ∃ path : ℝ → Space, path 0 = initial ∧ ContinuousOn path (Icc 0 horizon) ∧
      (∀ time ∈ Icc 0 horizon, HasDerivWithinAt path (coefficient time (path time)) (Icc 0 horizon) time) ∧
      ∀ time ∈ Icc 0 horizon, ‖path time‖ ≤ ‖initial‖ * Real.exp (bound * time) := by
  let radius := ‖initial‖ * Real.exp (bound * horizon) + 1
  have radiusPositive : 0 < radius := by dsimp [radius]; positivity
  let projection := closedBallProjection (Space := Space) radius radiusPositive.le
  let field := fun time state => coefficient time (projection state)
  have projectionBound (state : Space) : ‖projection state‖ ≤ radius := by
    simpa only [mem_closedBall, dist_zero_right] using (closedBallProjection_spec radius radiusPositive.le state).1
  have fieldLipschitz (time : ℝ) (inside : time ∈ Icc 0 horizon) : LipschitzWith bound (field time) := by
    have linearLipschitz : LipschitzWith bound (coefficient time) := by
      apply LipschitzWith.of_dist_le_mul
      intro first second
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact ((coefficient time).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (bounded time inside) (norm_nonneg _))
    simpa only [mul_one] using linearLipschitz.comp (lipschitz_closedBallProjection (Space := Space) radius radiusPositive.le)
  have fieldContinuous (state : Space) : ContinuousOn (fun time => field time state) (Icc 0 horizon) :=
    continuous.clm_apply continuousOn_const
  have fieldBounded (time : ℝ) (inside : time ∈ Icc 0 horizon) (state : Space) :
      ‖field time state‖ ≤ (bound * ⟨radius, radiusPositive.le⟩ : ℝ≥0) := by
    exact ((coefficient time).le_opNorm _).trans
      (mul_le_mul (bounded time inside) (projectionBound state) (norm_nonneg _) bound.coe_nonneg)
  obtain ⟨path, initialEquality, pathContinuous, derivative, _⟩ :=
    exists_solution_Icc_of_bounded_timeDependent_lipschitz nonnegative fieldLipschitz fieldContinuous fieldBounded initial
  have growth (time : ℝ) (inside : time ∈ Icc 0 horizon) : ‖path time‖ ≤ ‖initial‖ * Real.exp (bound * time) := by
    have estimate := norm_le_gronwallBound_of_norm_deriv_right_le (K := (bound : ℝ)) (ε := 0) (δ := ‖initial‖)
      pathContinuous
      (fun other otherInside => (derivative other ⟨otherInside.1, otherInside.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem otherInside))
      (by rw [initialEquality])
      (fun other otherInside => by
        rw [add_zero]
        exact ((coefficient other).le_opNorm _).trans
          (mul_le_mul (bounded other ⟨otherInside.1, otherInside.2.le⟩)
            (norm_closedBallProjection_le radius radiusPositive.le (path other)) (norm_nonneg _) bound.coe_nonneg)) time inside
    simpa only [gronwallBound_ε0, sub_zero] using estimate
  have projectionEquality (time : ℝ) (inside : time ∈ Icc 0 horizon) : projection (path time) = path time := by
    apply closedBallProjection_eq_self radiusPositive.le
    rw [mem_closedBall, dist_zero_right]
    calc
      _ ≤ ‖initial‖ * Real.exp (bound * time) := growth time inside
      _ ≤ ‖initial‖ * Real.exp (bound * horizon) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left inside.2 bound.coe_nonneg)) (norm_nonneg _)
      _ ≤ radius := by dsimp [radius]; linarith
  refine ⟨path, initialEquality, pathContinuous, ?_, growth⟩
  intro time inside
  have result := derivative time inside
  change HasDerivWithinAt path (coefficient time (projection (path time))) (Icc 0 horizon) time at result
  rwa [projectionEquality time inside] at result

end EulerNonuniqueness
