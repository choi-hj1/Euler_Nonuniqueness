import Mathlib

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.General

variable {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]

theorem intervalIntegrable_exponential_translated_window
    (function : ℝ → Value) (rate start horizon : ℝ)
    (integrable : IntervalIntegrable (fun time => Real.exp (-rate * time) • function time)
      volume start (start + horizon)) :
    IntervalIntegrable (fun elapsed => Real.exp (-rate * elapsed) • function (start + elapsed))
      volume 0 horizon := by
  have shifted : IntervalIntegrable
      (fun elapsed => Real.exp (-rate * (start + elapsed)) • function (start + elapsed)) volume 0 horizon := by
    simpa only [sub_self, add_sub_cancel_left] using integrable.comp_add_left start
  have scaled := shifted.smul (Real.exp (rate * start))
  convert scaled using 1
  funext elapsed
  change Real.exp (-rate * elapsed) • function (start + elapsed) =
    Real.exp (rate * start) • (Real.exp (-rate * (start + elapsed)) • function (start + elapsed))
  rw [smul_smul, ← Real.exp_add]
  congr 2
  ring

theorem exponential_integral_original_window_split
    [CompleteSpace Value]
    (function : ℝ → Value) (rate start horizon : ℝ)
    (initialIntegrable : IntervalIntegrable (fun time => Real.exp (-rate * time) • function time)
      volume 0 start)
    (windowIntegrable : IntervalIntegrable (fun time => Real.exp (-rate * time) • function time)
      volume start (start + horizon)) :
    (∫ time in (0 : ℝ)..(start + horizon), Real.exp (-rate * time) • function time) =
      (∫ time in (0 : ℝ)..start, Real.exp (-rate * time) • function time) +
        Real.exp (-rate * start) •
          ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-rate * elapsed) • function (start + elapsed) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals initialIntegrable windowIntegrable]
  congr 1
  have translated := intervalIntegral.integral_comp_add_left
    (fun time => Real.exp (-rate * time) • function time) start (a := 0) (b := horizon)
  rw [add_zero] at translated
  rw [← translated, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro elapsed _
  dsimp only
  rw [smul_smul, ← Real.exp_add]
  congr 2
  ring

end EulerNonuniqueness.General
