import Mathlib

noncomputable section

open Set Filter
open scoped Topology

theorem continuous_contactTime_of_strict_crossing
    {parameterType : Type*} [TopologicalSpace parameterType] [SequentialSpace parameterType]
    {monitor : parameterType → ℝ → ℝ} {contactTime : parameterType → ℝ} {horizon : ℝ}
    (jointContinuous : Continuous (fun point : parameterType × ℝ => monitor point.1 point.2))
    (timeBounds : ∀ parameter, contactTime parameter ∈ Icc 0 horizon)
    (contact : ∀ parameter, monitor parameter (contactTime parameter) = 0)
    (strictBefore : ∀ parameter time, 0 ≤ time → time < contactTime parameter → monitor parameter time < 0)
    (crossing : ∀ parameter epsilon, 0 < epsilon → ∃ time,
      contactTime parameter < time ∧ time < contactTime parameter + epsilon ∧ 0 < monitor parameter time) :
    Continuous contactTime := by
  apply continuous_iff_seqContinuous.mpr
  intro parameters parameter parametersTendsto
  apply tendsto_of_subseq_tendsto
  intro subsequence subsequenceTendsto
  have parametersAlong : Tendsto (fun index => parameters (subsequence index)) atTop (𝓝 parameter) :=
    parametersTendsto.comp subsequenceTendsto
  obtain ⟨limit, limitInside, further, furtherStrict, contactTimesTendsto⟩ :=
    isCompact_Icc.tendsto_subseq (fun index => timeBounds (parameters (subsequence index)))
  have selectedParameters : Tendsto (fun index => parameters (subsequence (further index))) atTop (𝓝 parameter) :=
    parametersAlong.comp furtherStrict.tendsto_atTop
  have jointLimit : Tendsto
      (fun index => monitor (parameters (subsequence (further index)))
        (contactTime (parameters (subsequence (further index))))) atTop (𝓝 (monitor parameter limit)) :=
    jointContinuous.tendsto (parameter, limit) |>.comp (selectedParameters.prodMk_nhds contactTimesTendsto)
  have limitContact : monitor parameter limit = 0 := by
    have zeroLimit : Tendsto
        (fun index => monitor (parameters (subsequence (further index)))
          (contactTime (parameters (subsequence (further index))))) atTop (𝓝 0) := by
      simpa only [contact] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique jointLimit zeroLimit
  have limitNotBefore : contactTime parameter ≤ limit := by
    by_contra failure
    have negative := strictBefore parameter limit limitInside.1 (lt_of_not_ge failure)
    linarith
  have limitNotAfter : limit ≤ contactTime parameter := by
    by_contra failure
    have gapPositive : 0 < limit - contactTime parameter := sub_pos.mpr (lt_of_not_ge failure)
    obtain ⟨crossTime, afterContact, beforeLimit, positive⟩ := crossing parameter
      (limit - contactTime parameter) gapPositive
    have crossBeforeLimit : crossTime < limit := by linarith
    have eventuallyAfter : ∀ᶠ index in atTop,
        crossTime < contactTime (parameters (subsequence (further index))) :=
      contactTimesTendsto.eventually (eventually_gt_nhds crossBeforeLimit)
    have monitorTendsto : Tendsto
        (fun index => monitor (parameters (subsequence (further index))) crossTime) atTop
        (𝓝 (monitor parameter crossTime)) :=
      (jointContinuous.comp (continuous_id.prodMk continuous_const)).tendsto parameter |>.comp selectedParameters
    have nonpositive : monitor parameter crossTime ≤ 0 := le_of_tendsto monitorTendsto
      (eventuallyAfter.mono (fun index later => (strictBefore _ crossTime
        ((timeBounds parameter).1.trans afterContact.le) later).le))
    linarith
  have limitIdentity : limit = contactTime parameter := le_antisymm limitNotAfter limitNotBefore
  exact ⟨further, by simpa only [limitIdentity, Function.comp_def] using contactTimesTendsto⟩
