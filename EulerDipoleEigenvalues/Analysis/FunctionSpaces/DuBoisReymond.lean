module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The du Bois-Reymond lemma on an interval

Blueprint: `lem:du-bois-reymond`.

If `∫ φ m = ∫ φ' G` for every smooth `φ` with compact support in `(α, β)`, then `G' = -m` in
the sense of distributions, so `G(h) - G(h') = ∫_h^{h'} m` for all `h < h'` outside a null set.

Proof: with `M(x) = ∫_c^x m`, integration by parts for the absolutely continuous `M` gives
`∫ φ' (G + M) = 0`. For a test function `g` and a fixed bump `φ₀` with `∫ φ₀ = 1`, the function
`g - (∫ g) φ₀` is the derivative of a test function, so `∫ g (G + M - k) = 0` with
`k = ∫ φ₀ (G + M)`, and `G + M = k` almost everywhere by the fundamental lemma of the calculus
of variations.
-/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open MeasureTheory Set Filter Topology
open scoped ContDiff

/-- A continuous function vanishing outside `[a, b]` vanishes at `a`. -/
private theorem eq_zero_left_of_support {φ : ℝ → ℝ} (hφ : Continuous φ) {a b : ℝ}
    (hsupp : ∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) : φ a = 0 := by
  have h : Tendsto φ (𝓝[<] a) (𝓝 (φ a)) := hφ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h0 : Tendsto φ (𝓝[<] a) (𝓝 0) := by
    refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s (hs : s < a) ↦ ?_)
    by_contra hne
    linarith [(hsupp s (Ne.symm hne)).1]
  exact tendsto_nhds_unique h h0

/-- A continuous function vanishing outside `[a, b]` vanishes at `b`. -/
private theorem eq_zero_right_of_support {φ : ℝ → ℝ} (hφ : Continuous φ) {a b : ℝ}
    (hsupp : ∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) : φ b = 0 := by
  have h : Tendsto φ (𝓝[>] b) (𝓝 (φ b)) := hφ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h0 : Tendsto φ (𝓝[>] b) (𝓝 0) := by
    refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s (hs : b < s) ↦ ?_)
    by_contra hne
    linarith [(hsupp s (Ne.symm hne)).2]
  exact tendsto_nhds_unique h h0

/-- For `φ` continuous and vanishing outside `[a, b]`, integrals of `φ F` over `ℝ` are interval
    integrals. -/
private theorem integral_mul_eq_intervalIntegral {φ : ℝ → ℝ} (hφ : Continuous φ) {a b : ℝ}
    (hab : a ≤ b) (hsupp : ∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) (F : ℝ → ℝ) :
    ∫ s, φ s * F s = ∫ s in a..b, φ s * F s := by
  rw [intervalIntegral.integral_of_le hab]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦ ?_).symm
  have : φ s = 0 := by
    by_contra hne
    obtain ⟨h1, h2⟩ := hsupp s hne
    rcases h1.lt_or_eq with h1 | h1
    · exact hs ⟨h1, h2⟩
    · exact hne (h1 ▸ eq_zero_left_of_support hφ hsupp)
  simp [this]

/-- The derivative of a smooth function vanishing outside `[a, b]` vanishes outside `[a, b]`. -/
private theorem deriv_support {φ : ℝ → ℝ} {a b : ℝ} (hsupp : ∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) :
    ∀ s, deriv φ s ≠ 0 → a ≤ s ∧ s ≤ b := by
  intro s hs
  by_contra hns
  apply hs
  have hev : φ =ᶠ[𝓝 s] fun _ ↦ 0 := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds (show s ∉ Icc a b from hns)] with t ht
    by_contra hne
    exact ht (hsupp t hne)
  rw [hev.deriv_eq, deriv_const]

/-- The du Bois-Reymond lemma (`lem:du-bois-reymond`): a locally integrable `G` whose
    distributional derivative is `-m` agrees almost everywhere with a primitive of `-m`. -/
theorem exists_null_sub_eq_intervalIntegral {m G : ℝ → ℝ} {α β : ℝ}
    (hm : ∀ a b, α < a → b < β → IntegrableOn m (Icc a b))
    (hG : ∀ a b, α < a → b < β → IntegrableOn G (Icc a b))
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → ∀ a b, α < a → b < β →
      (∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) → ∫ s, φ s * m s = ∫ s, deriv φ s * G s) :
    ∃ N : Set ℝ, volume N = 0 ∧ ∀ h h' : ℝ, α < h → h < h' → h' < β → h ∉ N → h' ∉ N →
      ∫ s in h..h', m s = G h - G h' := by
  by_cases hαβ : α < β
  swap
  · exact ⟨∅, by simp, fun h h' h1 h2 h3 _ _ ↦ absurd (h1.trans (h2.trans h3)) hαβ⟩
  set U : Set ℝ := Ioo α β
  set c : ℝ := (α + β) / 2
  have hcU : c ∈ U := ⟨by simp only [c]; linarith, by simp only [c]; linarith⟩
  have hmI {x y : ℝ} (hx : x ∈ U) (hy : y ∈ U) : IntervalIntegrable m volume x y := by
    rw [intervalIntegrable_iff]
    exact (hm (min x y) (max x y) (lt_min hx.1 hy.1) (max_lt hx.2 hy.2)).mono_set
      uIoc_subset_uIcc
  set M : ℝ → ℝ := fun x ↦ ∫ t in c..x, m t
  set D : ℝ → ℝ := fun x ↦ G x + M x
  -- Step 1: `∫ φ' D = 0` for test functions `φ` whose support interval contains `c`.
  have hD0 : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → ∀ a b, α < a → b < β → a ≤ c → c ≤ b →
      (∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) → ∫ s, deriv φ s * D s = 0 := by
    intro φ hφ a b ha hb hac hcb hsupp
    have hab : a ≤ b := hac.trans hcb
    have haU : a ∈ U := ⟨ha, by linarith [hcU.2]⟩
    have hbU : b ∈ U := ⟨by linarith [hcU.1], hb⟩
    have hφc : Continuous φ := hφ.continuous
    have hdc : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
    have hdsupp := deriv_support hsupp
    have hint := h φ hφ a b ha hb hsupp
    have hIm := hmI haU hbU
    have hcab : c ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ⟨hac, hcb⟩
    have hMac : AbsolutelyContinuousOnInterval M a b :=
      hIm.absolutelyContinuousOnInterval_intervalIntegral hcab
    have hφac : AbsolutelyContinuousOnInterval φ a b :=
      (hφ.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
    have hibp := hφac.integral_mul_deriv_eq_deriv_mul hMac
    rw [eq_zero_left_of_support hφc hsupp, eq_zero_right_of_support hφc hsupp, zero_mul,
      zero_mul, sub_zero, zero_sub] at hibp
    have hdM : ∫ x in a..b, φ x * deriv M x = ∫ x in a..b, φ x * m x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hIm.ae_hasDerivAt_integral] with x hx hxI
      rw [(hx (uIoc_subset_uIcc hxI) c hcab).deriv]
    rw [integral_mul_eq_intervalIntegral hφc hab hsupp,
      integral_mul_eq_intervalIntegral hdc hab hdsupp] at hint
    rw [integral_mul_eq_intervalIntegral hdc hab hdsupp]
    have hGI : IntervalIntegrable G volume a b :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 (hG a b ha hb)
    have hGI' : IntervalIntegrable (fun x ↦ deriv φ x * G x) volume a b :=
      hGI.continuousOn_mul hdc.continuousOn
    have hMI' : IntervalIntegrable (fun x ↦ deriv φ x * M x) volume a b :=
      (hdc.continuousOn.mul hMac.continuousOn).intervalIntegrable
    simp only [D, mul_add]
    rw [intervalIntegral.integral_add hGI' hMI']
    linarith
  -- Step 2: `D` is locally integrable on `U`.
  have hbounds {K : Set ℝ} (hKU : K ⊆ U) (hKc : IsCompact K) (hcK : c ∈ K) :
      α < sInf K ∧ sSup K < β ∧ sInf K ≤ c ∧ c ≤ sSup K ∧ K ⊆ Icc (sInf K) (sSup K) := by
    have hne : K.Nonempty := ⟨c, hcK⟩
    exact ⟨(hKU (hKc.sInf_mem hne)).1, (hKU (hKc.sSup_mem hne)).2,
      csInf_le hKc.bddBelow hcK, le_csSup hKc.bddAbove hcK,
      fun x hx ↦ ⟨csInf_le hKc.bddBelow hx, le_csSup hKc.bddAbove hx⟩⟩
  have hDint {a b : ℝ} (ha : α < a) (hb : b < β) (hac : a ≤ c) (hcb : c ≤ b) :
      IntegrableOn D (Icc a b) := by
    have hab : a ≤ b := hac.trans hcb
    have haU : a ∈ U := ⟨ha, by linarith [hcU.2]⟩
    have hbU : b ∈ U := ⟨by linarith [hcU.1], hb⟩
    have hcab : c ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ⟨hac, hcb⟩
    have hMc : ContinuousOn M (Icc a b) := by
      have := ((hmI haU hbU).absolutelyContinuousOnInterval_intervalIntegral hcab).continuousOn
      rwa [uIcc_of_le hab] at this
    exact (hG a b ha hb).add (hMc.integrableOn_Icc)
  have hDloc : LocallyIntegrableOn D U volume := by
    rw [locallyIntegrableOn_iff isOpen_Ioo.isLocallyClosed]
    intro K hKU hKc
    obtain ⟨h1, h2, h3, h4, h5⟩ := hbounds (union_subset hKU (singleton_subset_iff.2 hcU))
      (hKc.union isCompact_singleton) (Or.inr rfl)
    exact (hDint h1 h2 h3 h4).mono_set (subset_union_left.trans h5)
  -- Step 3: a bump `φ₀` with `∫ φ₀ = 1`, supported in `U` around `c`.
  set r : ℝ := (β - α) / 8
  have hr : 0 < r := by simp only [r]; linarith
  let bump : ContDiffBump c := ⟨r, 2 * r, hr, by linarith⟩
  set φ₀ : ℝ → ℝ := bump.normed volume
  set k : ℝ := ∫ s, φ₀ s * D s
  -- Step 4: `D - k` integrates to zero against every test function on `U`.
  have hfund := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (f := fun x ↦ D x - k) (μ := volume) (hDloc.sub (locallyIntegrableOn_const k)) ?_
  swap
  · intro g hg hgc hgU
    have hball : Metric.closedBall c (2 * r) ⊆ U := by
      rw [Real.closedBall_eq_Icc]
      intro x hx
      exact ⟨by simp only [c, r] at hx; linarith [hx.1], by simp only [c, r] at hx; linarith [hx.2]⟩
    set K : Set ℝ := tsupport g ∪ Metric.closedBall c (2 * r)
    obtain ⟨ha₀, hb₀, hac, hcb, hK⟩ := hbounds (union_subset hgU hball)
      (hgc.isCompact.union (isCompact_closedBall c _))
      (Or.inr (Metric.mem_closedBall_self (by linarith)))
    set a₀ := sInf K
    set b₀ := sSup K
    have hab : a₀ ≤ b₀ := hac.trans hcb
    have hgs : ∀ s, g s ≠ 0 → a₀ ≤ s ∧ s ≤ b₀ := fun s hs ↦
      hK (Or.inl (subset_tsupport g hs))
    have hφ₀s : ∀ s, φ₀ s ≠ 0 → a₀ ≤ s ∧ s ≤ b₀ := by
      intro s hs
      have : s ∈ Function.support φ₀ := hs
      rw [ContDiffBump.support_normed_eq] at this
      exact hK (Or.inr (Metric.ball_subset_closedBall this))
    have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
    have hφ₀c : ContDiff ℝ ∞ φ₀ := bump.contDiff_normed (n := ⊤)
    have hφ₀i : Integrable φ₀ :=
      hφ₀c.continuous.integrable_of_hasCompactSupport bump.hasCompactSupport_normed
    set I : ℝ := ∫ s, g s
    set ψ : ℝ → ℝ := fun s ↦ g s - I * φ₀ s
    have hψc : Continuous ψ := hg.continuous.sub (continuous_const.mul hφ₀c.continuous)
    have hψs : ∀ s, ψ s ≠ 0 → a₀ ≤ s ∧ s ≤ b₀ := by
      intro s hs
      by_cases hgs0 : g s = 0
      · have : φ₀ s ≠ 0 := by
          intro h0
          apply hs
          simp [ψ, hgs0, h0]
        exact hφ₀s s this
      · exact hgs s hgs0
    have hψl : ∀ s, s ≤ a₀ → ψ s = 0 := by
      intro s hs
      by_contra hne
      have h1 := (hψs s hne).1
      exact hne ((le_antisymm hs h1) ▸ eq_zero_left_of_support hψc hψs)
    have hψr : ∀ s, b₀ ≤ s → ψ s = 0 := by
      intro s hs
      by_contra hne
      have h2 := (hψs s hne).2
      exact hne ((le_antisymm h2 hs) ▸ eq_zero_right_of_support hψc hψs)
    have hψint : ∫ s in a₀..b₀, ψ s = 0 := by
      rw [intervalIntegral.integral_of_le hab]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦ ?_]
      · simp only [ψ]
        rw [integral_sub hgi (hφ₀i.const_mul I), integral_const_mul,
          bump.integral_normed (μ := volume), mul_one, sub_self]
      · simp only [mem_Ioc, not_and_or, not_lt, not_le] at hs
        rcases hs with hs | hs
        · exact hψl s hs
        · exact hψr s hs.le
    set φ : ℝ → ℝ := fun s ↦ ∫ t in a₀..s, ψ t
    have hφd : ∀ s, HasDerivAt φ (ψ s) s := fun s ↦
      (hψc.integral_hasStrictDerivAt a₀ s).hasDerivAt
    have hderiv : deriv φ = ψ := funext fun s ↦ (hφd s).deriv
    have hφs : ContDiff ℝ ∞ φ := by
      refine contDiff_infty_iff_deriv.2 ⟨fun s ↦ (hφd s).differentiableAt, ?_⟩
      rw [hderiv]
      exact hg.sub (contDiff_const.mul hφ₀c)
    have hzero {u v : ℝ} (huv : ∀ t ∈ uIcc u v, ψ t = 0) : ∫ t in u..v, ψ t = 0 := by
      rw [intervalIntegral.integral_congr huv]
      simp
    have hφsupp : ∀ s, φ s ≠ 0 → a₀ ≤ s ∧ s ≤ b₀ := by
      intro s hs
      by_contra hns
      apply hs
      rcases not_and_or.1 hns with h1 | h1
      · refine hzero fun t ht ↦ hψl t ?_
        rw [uIcc_of_ge (le_of_not_ge h1)] at ht
        exact ht.2
      · have hsb : b₀ ≤ s := (lt_of_not_ge h1).le
        change ∫ t in a₀..s, ψ t = 0
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (hψc.intervalIntegrable a₀ b₀) (hψc.intervalIntegrable b₀ s), hψint, zero_add]
        refine hzero fun t ht ↦ hψr t ?_
        rw [uIcc_of_le hsb] at ht
        exact ht.1
    have hmain := hD0 φ hφs a₀ b₀ ha₀ hb₀ hac hcb hφsupp
    rw [hderiv] at hmain
    -- Integrability of `g D` and `φ₀ D`, which vanish outside `[a₀, b₀]`.
    have hDI := hDint ha₀ hb₀ hac hcb
    have hint {u : ℝ → ℝ} (hu : Continuous u) (hus : ∀ s, u s ≠ 0 → a₀ ≤ s ∧ s ≤ b₀) :
        Integrable fun s ↦ u s * D s := by
      refine (hDI.continuousOn_mul hu.continuousOn
        isCompact_Icc).integrable_of_forall_notMem_eq_zero fun s hs ↦ ?_
      have : u s = 0 := by
        by_contra hne
        exact hs (hus s hne)
      simp [this]
    have hgD := hint hg.continuous hgs
    have hφ₀D := hint hφ₀c.continuous hφ₀s
    have h1 : ∫ s, ψ s * D s = (∫ s, g s * D s) - I * k := by
      simp only [ψ, sub_mul, mul_assoc]
      rw [integral_sub hgD (hφ₀D.const_mul I), integral_const_mul]
    have h2 : ∫ s, g s • (D s - k) = (∫ s, g s * D s) - k * I := by
      simp only [smul_eq_mul, mul_sub]
      rw [integral_sub hgD (hgi.mul_const k), integral_mul_const, mul_comm]
    rw [h2]
    linarith [mul_comm I k]
  -- Step 5: conclusion.
  set N : Set ℝ := {x | x ∈ U ∧ D x - k ≠ 0}
  have hN : volume N = 0 := by
    simpa only [ae_iff, not_imp] using hfund
  refine ⟨N, hN, fun x y hx hxy hy hxN hyN ↦ ?_⟩
  have hxU : x ∈ U := ⟨hx, hxy.trans hy⟩
  have hyU : y ∈ U := ⟨hx.trans hxy, hy⟩
  have hDx : D x = k := by
    by_contra hne
    exact hxN ⟨hxU, sub_ne_zero.2 hne⟩
  have hDy : D y = k := by
    by_contra hne
    exact hyN ⟨hyU, sub_ne_zero.2 hne⟩
  have hsub := intervalIntegral.integral_interval_sub_left (hmI hcU hyU) (hmI hcU hxU)
  simp only [D, M] at hDx hDy
  linarith

end EulerDipoleEigenvalues
