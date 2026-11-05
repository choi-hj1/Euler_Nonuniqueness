import EulerNonuniqueness.General.TwoRateExponentialResponse

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

theorem weighted_quadratic_profile_integral_le_of_exposure
    {shape state : ℝ → ℝ}
    {finish origin rate omega shapeMagnitude stateMagnitude seed endpoint : ℝ}
    (finishNonnegative : 0 ≤ finish) (ratePositive : 0 < rate)
    (omegaNonnegative : 0 ≤ omega) (omegaRate : omega ≤ rate)
    (shapeMagnitudeNonnegative : 0 ≤ shapeMagnitude)
    (stateMagnitudeNonnegative : 0 ≤ stateMagnitude) (seedPositive : 0 < seed)
    (integrable : IntervalIntegrable
      (fun time => Real.exp (-rate * time) * (shape time * (shape time + state time))) volume 0 finish)
    (shapeNonnegative : ∀ time ∈ Icc 0 finish, 0 ≤ shape time)
    (stateNonnegative : ∀ time ∈ Icc 0 finish, 0 ≤ state time)
    (shapeProfile : ∀ time ∈ Icc 0 finish,
      shape time ≤ shapeMagnitude * seed * Real.exp (rate * (time - origin)))
    (stateProfile : ∀ time ∈ Icc 0 finish,
      state time ≤ stateMagnitude * seed * Real.exp (rate * (time - origin)))
    (exposure : seed * Real.exp (rate * (finish - origin)) ≤ endpoint) :
    omega * Real.exp (rate * origin) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * (shape time * (shape time + state time))) ≤
      shapeMagnitude * (shapeMagnitude + stateMagnitude) * endpoint * seed := by
  let bound := shapeMagnitude * (shapeMagnitude + stateMagnitude) * seed ^ 2
  have boundNonnegative : 0 ≤ bound := by dsimp only [bound]; positivity
  have profile (time : ℝ) (inside : time ∈ Icc 0 finish) :
      shape time * (shape time + state time) ≤ bound * Real.exp ((2 * rate) * (time - origin)) := by
    have comparison := mul_le_mul (shapeProfile time inside)
      (add_le_add (shapeProfile time inside) (stateProfile time inside))
      (add_nonneg (shapeNonnegative time inside) (stateNonnegative time inside))
      (by positivity : 0 ≤ shapeMagnitude * seed * Real.exp (rate * (time - origin)))
    apply comparison.trans_eq
    have identity : Real.exp (rate * (time - origin)) ^ 2 = Real.exp ((2 * rate) * (time - origin)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = bound * Real.exp (rate * (time - origin)) ^ 2 := by dsimp only [bound]; ring
      _ = _ := by rw [identity]
  have response := intervalIntegral.exp_mul_integral_le_of_faster_exponential_majorant
    (firstRate := rate) (secondRate := 2 * rate) finishNonnegative (by linarith only [ratePositive])
    boundNonnegative integrable profile
  have multiplied := mul_le_mul_of_nonneg_left response
    (show 0 ≤ omega * Real.exp (rate * (origin - finish)) by positivity)
  have cancellation : Real.exp (rate * (origin - finish)) * Real.exp (rate * finish) =
      Real.exp (rate * origin) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have exponentIdentity : Real.exp (rate * (origin - finish)) * Real.exp ((2 * rate) * (finish - origin)) =
      Real.exp (rate * (finish - origin)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have normalized : omega * Real.exp (rate * origin) *
      (∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * (shape time * (shape time + state time))) ≤
        (omega / rate) * bound * Real.exp (rate * (finish - origin)) := by
    calc
      _ = (omega * Real.exp (rate * (origin - finish))) *
          (Real.exp (rate * finish) *
            (∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * (shape time * (shape time + state time)))) := by
        calc
          _ = omega * (Real.exp (rate * origin) *
              (∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * (shape time * (shape time + state time)))) := by ring
          _ = omega * ((Real.exp (rate * (origin - finish)) * Real.exp (rate * finish)) *
              (∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * (shape time * (shape time + state time)))) := by rw [cancellation]
          _ = _ := by ring
      _ ≤ _ := multiplied
      _ = _ := by
        rw [show 2 * rate - rate = rate by ring]
        calc
          _ = (omega / rate) * bound *
              (Real.exp (rate * (origin - finish)) * Real.exp ((2 * rate) * (finish - origin))) := by ring
          _ = _ := by rw [exponentIdentity]
  have ratioBound : omega / rate ≤ 1 := (div_le_one ratePositive).mpr omegaRate
  have reduced := normalized.trans (by
    convert mul_le_mul_of_nonneg_right ratioBound
      (mul_nonneg boundNonnegative (Real.exp_pos (rate * (finish - origin))).le) using 1
    ring)
  have finalBound := mul_le_mul_of_nonneg_left exposure
    (show 0 ≤ shapeMagnitude * (shapeMagnitude + stateMagnitude) * seed by positivity)
  apply reduced.trans
  convert finalBound using 1 <;> dsimp only [bound] <;> ring

end EulerNonuniqueness.General
