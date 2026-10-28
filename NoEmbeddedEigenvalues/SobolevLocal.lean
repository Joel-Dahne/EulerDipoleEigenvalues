import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import NoEmbeddedEigenvalues.LiftTorus
import NoEmbeddedEigenvalues.DiagonalCalculus

/-!
# Sobolev spaces on open subsets of the plane

Blueprint: `def:weak-derivative-local`, `def:sobolev-local`, `lem:weak-derivative-basic`,
`lem:weak-derivative-classical`. `lem:local-to-global` is in `LocalToGlobal.lean`.
The ACL, L², H² and fractional trace proofs live in the trace modules.

Local Sobolev spaces are defined on open sets `U ⊆ ℝ²`, the lift of the torus, through
weak derivatives tested against smooth functions with compact support in `U`. The
weighted spaces replace Lebesgue measure on `U` by a weighted measure. Only the
definitions and the first layer of facts are here: linearity and restriction, classical
derivatives are weak derivatives, and multiplication by a smooth cutoff.
The test-annihilator criterion and a.e. uniqueness of weak partial derivatives live here
so the action-angle chain rules can use them without importing `CellPeriodization.lean`.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- A test function on `U`: smooth, with compact support contained in `U`. This is the
    unbundled form of Mathlib's `TestFunction`. -/
structure IsTestFunctionOn (U : Set (ℝ × ℝ)) (φ : ℝ × ℝ → ℂ) : Prop where
  contDiff : ContDiff ℝ ∞ φ
  hasCompactSupport : HasCompactSupport φ
  tsupport_subset : tsupport φ ⊆ U

/-- The coordinate partial derivative: `j = 0` is `∂ₓ`, `j = 1` is `∂_y`. -/
def coordPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (j : Fin 2)
    (u : ℝ × ℝ → E) : ℝ × ℝ → E :=
  if j = 0 then partialX u else partialY u

/-- `h` is the weak `j`-th partial derivative of `g` on `U`: both are locally integrable on
    `U` and `∫ g ∂ⱼφ = -∫ h φ` for every test function `φ` on `U`. -/
def HasWeakPartialOn (U : Set (ℝ × ℝ)) (j : Fin 2) (g h : ℝ × ℝ → ℂ) : Prop :=
  LocallyIntegrableOn g U ∧ LocallyIntegrableOn h U ∧
    ∀ φ, IsTestFunctionOn U φ → ∫ p, g p * coordPartial j φ p = -∫ p, h p * φ p

/-- `g ∈ Hᵏ(U)` for the measure `μ` on `U`: `g` and all weak derivatives up to order `k`
    exist and lie in `L²(μ)`. With `μ = volume.restrict U` this is the usual `Hᵏ(U)`; a
    weighted measure gives the weighted spaces. -/
def MemSobolevOnWith (μ : Measure (ℝ × ℝ)) (U : Set (ℝ × ℝ)) : ℕ → (ℝ × ℝ → ℂ) → Prop
  | 0, g => MemLp g 2 μ
  | k + 1, g => MemLp g 2 μ ∧ ∀ j, ∃ h, HasWeakPartialOn U j g h ∧ MemSobolevOnWith μ U k h

/-- `g ∈ Hᵏ(U)`. -/
def MemSobolevOn (k : ℕ) (U : Set (ℝ × ℝ)) (g : ℝ × ℝ → ℂ) : Prop :=
  MemSobolevOnWith (volume.restrict U) U k g

/-- `g ∈ Hᵏ(U, w)`: weak derivatives up to order `k` in `L²(U, w dx)`. -/
def MemWeightedSobolevOn (k : ℕ) (U : Set (ℝ × ℝ)) (w : ℝ × ℝ → ℝ) (g : ℝ × ℝ → ℂ) : Prop :=
  MemSobolevOnWith ((volume.restrict U).withDensity fun p ↦ ENNReal.ofReal (w p)) U k g

/-- `g ∈ Hᵏ_loc(U)`: `g ∈ Hᵏ(V)` for every open `V` with compact closure in `U`. -/
def MemSobolevLocOn (k : ℕ) (U : Set (ℝ × ℝ)) (g : ℝ × ℝ → ℂ) : Prop :=
  ∀ V, IsOpen V → IsCompact (closure V) → closure V ⊆ U → MemSobolevOn k V g

/-! ### Basic facts -/

section Basic

variable {U V : Set (ℝ × ℝ)} {g h g' h' : ℝ × ℝ → ℂ} {j : Fin 2}

/-- A locally integrable function times a continuous function with compact support inside
    `U` is integrable. -/
theorem integrable_mul_of_tsupport_subset (hg : LocallyIntegrableOn g U)
    {ψ : ℝ × ℝ → ℂ} (hψ : Continuous ψ) (hs : HasCompactSupport ψ) (hsub : tsupport ψ ⊆ U) :
    Integrable (fun p ↦ g p * ψ p) := by
  have hK : IsCompact (tsupport ψ) := hs
  have hi : IntegrableOn (fun p ↦ g p * ψ p) (tsupport ψ) :=
    (hg.integrableOn_compact_subset hsub hK).mul_continuousOn hψ.continuousOn hK
  refine hi.integrable_of_forall_notMem_eq_zero fun p hp ↦ ?_
  rw [image_eq_zero_of_notMem_tsupport hp, mul_zero]

/-- A locally integrable function on an open set with zero integral against every test
function vanishes almost everywhere there. -/
theorem ae_eq_zero_of_forall_test (hU : IsOpen U) {h : ℝ × ℝ → ℂ}
    (hh : LocallyIntegrableOn h U) (h0 : ∀ φ, IsTestFunctionOn U φ → ∫ p, h p * φ p = 0) :
    ∀ᵐ p, p ∈ U → h p = 0 := by
  refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hh fun g hg hgc hgU ↦ ?_
  have ht : IsTestFunctionOn U (fun p ↦ (g p : ℂ)) :=
    ⟨Complex.ofRealCLM.contDiff.comp hg, hgc.comp_left Complex.ofReal_zero,
      (tsupport_comp_subset Complex.ofReal_zero g).trans hgU⟩
  rw [← h0 _ ht]
  congr 1
  funext p
  rw [Complex.real_smul, mul_comm]

/-- Weak partial derivatives are unique almost everywhere. -/
theorem HasWeakPartialOn.ae_eq (hU : IsOpen U) {j : Fin 2} {F d d' : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn U j F d) (hd' : HasWeakPartialOn U j F d') :
    ∀ᵐ p, p ∈ U → d p = d' p := by
  have h := ae_eq_zero_of_forall_test hU (hd.2.1.sub hd'.2.1) fun φ hφ ↦ by
    have i := integrable_mul_of_tsupport_subset hd.2.1 hφ.contDiff.continuous
      hφ.hasCompactSupport hφ.tsupport_subset
    have i' := integrable_mul_of_tsupport_subset hd'.2.1 hφ.contDiff.continuous
      hφ.hasCompactSupport hφ.tsupport_subset
    simp only [Pi.sub_apply, sub_mul]
    rw [integral_sub i i', ← neg_neg (∫ p, d p * φ p), ← neg_neg (∫ p, d' p * φ p),
      ← hd.2.2 φ hφ, ← hd'.2.2 φ hφ, sub_self]
  filter_upwards [h] with p hp hpU
  exact sub_eq_zero.1 (hp hpU)

theorem tsupport_partialX_subset (φ : ℝ × ℝ → ℂ) : tsupport (partialX φ) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro p hp
  by_contra hq
  apply hp
  apply partialX_eq_zero_of_eventually
  filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hq] with q hq'
  exact image_eq_zero_of_notMem_tsupport hq'

theorem tsupport_partialY_subset (φ : ℝ × ℝ → ℂ) : tsupport (partialY φ) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro p hp
  by_contra hq
  apply hp
  apply partialY_eq_zero_of_eventually
  filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hq] with q hq'
  exact image_eq_zero_of_notMem_tsupport hq'

theorem tsupport_coordPartial_subset (j : Fin 2) (φ : ℝ × ℝ → ℂ) :
    tsupport (coordPartial j φ) ⊆ tsupport φ := by
  unfold coordPartial
  split_ifs
  · exact tsupport_partialX_subset φ
  · exact tsupport_partialY_subset φ

theorem contDiff_coordPartial {n : ℕ} (j : Fin 2) {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ (n + 1) φ) :
    ContDiff ℝ n (coordPartial j φ) := by
  unfold coordPartial
  split_ifs
  · exact contDiff_partialX hφ
  · exact contDiff_partialY hφ

theorem IsTestFunctionOn.mono {φ : ℝ × ℝ → ℂ} (hφ : IsTestFunctionOn V φ) (hVU : V ⊆ U) :
    IsTestFunctionOn U φ :=
  ⟨hφ.contDiff, hφ.hasCompactSupport, hφ.tsupport_subset.trans hVU⟩

theorem IsTestFunctionOn.continuous_coordPartial {φ : ℝ × ℝ → ℂ} (hφ : IsTestFunctionOn U φ)
    (j : Fin 2) : Continuous (coordPartial j φ) :=
  (contDiff_coordPartial (n := 0) j (hφ.contDiff.of_le (by simp))).continuous

theorem IsTestFunctionOn.hasCompactSupport_coordPartial {φ : ℝ × ℝ → ℂ}
    (hφ : IsTestFunctionOn U φ) (j : Fin 2) : HasCompactSupport (coordPartial j φ) :=
  hφ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) (tsupport_coordPartial_subset j φ)

/-- Weak derivatives restrict to smaller sets. -/
theorem HasWeakPartialOn.mono (hd : HasWeakPartialOn U j g h) (hVU : V ⊆ U) :
    HasWeakPartialOn V j g h :=
  ⟨hd.1.mono_set hVU, hd.2.1.mono_set hVU, fun φ hφ ↦ hd.2.2 φ (hφ.mono hVU)⟩

/-- Weak derivatives on a measurable set are unchanged by a.e. changes on that set. -/
theorem HasWeakPartialOn.congr_ae_on {U : Set (ℝ × ℝ)} (hU : MeasurableSet U)
    {j : Fin 2} {g g' h h' : ℝ × ℝ → ℂ} (hd : HasWeakPartialOn U j g h)
    (hg : ∀ᵐ p, p ∈ U → g p = g' p) (hh : ∀ᵐ p, p ∈ U → h p = h' p) :
    HasWeakPartialOn U j g' h' := by
  refine ⟨hd.1.congr ((ae_restrict_iff' hU).mpr hg),
    hd.2.1.congr ((ae_restrict_iff' hU).mpr hh), fun φ hφ ↦ ?_⟩
  have e1 : (∫ p, g' p * coordPartial j φ p) = ∫ p, g p * coordPartial j φ p := by
    refine integral_congr_ae ?_
    filter_upwards [hg] with p hp
    by_cases hpU : p ∈ U
    · rw [hp hpU]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hpU (hφ.tsupport_subset
        (tsupport_coordPartial_subset j φ ht))), mul_zero, mul_zero]
  have e2 : (∫ p, h' p * φ p) = ∫ p, h p * φ p := by
    refine integral_congr_ae ?_
    filter_upwards [hh] with p hp
    by_cases hpU : p ∈ U
    · rw [hp hpU]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hpU (hφ.tsupport_subset ht)), mul_zero,
        mul_zero]
  rw [e1, e2]
  exact hd.2.2 φ hφ

/-- Weak derivatives are linear: sums. -/
theorem HasWeakPartialOn.add (hd : HasWeakPartialOn U j g h) (hd' : HasWeakPartialOn U j g' h') :
    HasWeakPartialOn U j (fun p ↦ g p + g' p) (fun p ↦ h p + h' p) := by
  refine ⟨hd.1.add hd'.1, hd.2.1.add hd'.2.1, fun φ hφ ↦ ?_⟩
  have i1 := integrable_mul_of_tsupport_subset hd.1 (hφ.continuous_coordPartial j)
    (hφ.hasCompactSupport_coordPartial j)
    ((tsupport_coordPartial_subset j φ).trans hφ.tsupport_subset)
  have i2 := integrable_mul_of_tsupport_subset hd'.1 (hφ.continuous_coordPartial j)
    (hφ.hasCompactSupport_coordPartial j)
    ((tsupport_coordPartial_subset j φ).trans hφ.tsupport_subset)
  have i3 := integrable_mul_of_tsupport_subset hd.2.1 hφ.contDiff.continuous
    hφ.hasCompactSupport hφ.tsupport_subset
  have i4 := integrable_mul_of_tsupport_subset hd'.2.1 hφ.contDiff.continuous
    hφ.hasCompactSupport hφ.tsupport_subset
  simp only [add_mul]
  rw [integral_add i1 i2, integral_add i3 i4, hd.2.2 φ hφ, hd'.2.2 φ hφ]
  ring

/-- Weak derivatives are linear: scalar multiples. -/
theorem HasWeakPartialOn.const_mul (hd : HasWeakPartialOn U j g h) (c : ℂ) :
    HasWeakPartialOn U j (fun p ↦ c * g p) (fun p ↦ c * h p) := by
  refine ⟨by simpa [Pi.smul_def] using hd.1.smul c, by simpa [Pi.smul_def] using hd.2.1.smul c,
    fun φ hφ ↦ ?_⟩
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, hd.2.2 φ hφ]
  ring

end Basic

/-! ### The spaces -/

section Spaces

variable {μ : Measure (ℝ × ℝ)} {U V : Set (ℝ × ℝ)} {g g' : ℝ × ℝ → ℂ}

theorem MemSobolevOnWith.memLp {k : ℕ} (h : MemSobolevOnWith μ U k g) : MemLp g 2 μ := by
  cases k with
  | zero => exact h
  | succ k => exact h.1

/-- `Hᵏ⁺¹ ⊆ Hᵏ`. -/
theorem MemSobolevOnWith.of_succ {k : ℕ} (h : MemSobolevOnWith μ U (k + 1) g) :
    MemSobolevOnWith μ U k g := by
  induction k generalizing g with
  | zero => exact h.1
  | succ k ih =>
    refine ⟨h.1, fun j ↦ ?_⟩
    obtain ⟨d, hd, hk⟩ := h.2 j
    exact ⟨d, hd, ih hk⟩

theorem MemSobolevOnWith.add {k : ℕ} (h : MemSobolevOnWith μ U k g)
    (h' : MemSobolevOnWith μ U k g') : MemSobolevOnWith μ U k (fun p ↦ g p + g' p) := by
  induction k generalizing g g' with
  | zero => exact MemLp.add (f := g) (g := g') h h'
  | succ k ih =>
    refine ⟨MemLp.add (f := g) (g := g') h.1 h'.1, fun j ↦ ?_⟩
    obtain ⟨d, hd, hk⟩ := h.2 j
    obtain ⟨d', hd', hk'⟩ := h'.2 j
    exact ⟨_, hd.add hd', ih hk hk'⟩

theorem MemSobolevOnWith.const_mul {k : ℕ} (h : MemSobolevOnWith μ U k g) (c : ℂ) :
    MemSobolevOnWith μ U k (fun p ↦ c * g p) := by
  induction k generalizing g with
  | zero => exact MemLp.const_mul h c
  | succ k ih =>
    refine ⟨MemLp.const_mul h.1 c, fun j ↦ ?_⟩
    obtain ⟨d, hd, hk⟩ := h.2 j
    exact ⟨_, hd.const_mul c, ih hk⟩

/-- `Hᵏ(U)` restricts to `Hᵏ(V)` for `V ⊆ U`. -/
theorem MemSobolevOn.mono {k : ℕ} (h : MemSobolevOn k U g) (hVU : V ⊆ U) :
    MemSobolevOn k V g := by
  induction k generalizing g with
  | zero => exact MemLp.mono_measure (Measure.restrict_mono hVU le_rfl) h
  | succ k ih =>
    refine ⟨MemLp.mono_measure (Measure.restrict_mono hVU le_rfl) h.1, fun j ↦ ?_⟩
    obtain ⟨d, hd, hk⟩ := h.2 j
    exact ⟨d, hd.mono hVU, ih hk⟩

theorem MemSobolevOn.memSobolevLocOn {k : ℕ} (h : MemSobolevOn k U g) :
    MemSobolevLocOn k U g := fun _ _ _ hV ↦ h.mono (subset_closure.trans hV)

theorem MemSobolevLocOn.of_succ {k : ℕ} (h : MemSobolevLocOn (k + 1) U g) :
    MemSobolevLocOn k U g := fun V hV hc hVU ↦ MemSobolevOnWith.of_succ (h V hV hc hVU)

theorem MemSobolevLocOn.add {k : ℕ} (h : MemSobolevLocOn k U g) (h' : MemSobolevLocOn k U g') :
    MemSobolevLocOn k U (fun p ↦ g p + g' p) :=
  fun V hV hc hVU ↦ MemSobolevOnWith.add (h V hV hc hVU) (h' V hV hc hVU)

end Spaces

/-! ### Classical derivatives are weak derivatives -/

section Classical

variable {u φ : ℝ × ℝ → ℂ}

/-- A function on `ℝ` with compact support tends to zero at `±∞`. -/
theorem tendsto_zero_of_hasCompactSupport {F : ℝ → ℂ} (hF : HasCompactSupport F) :
    Tendsto F atTop (𝓝 0) ∧ Tendsto F atBot (𝓝 0) := by
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at hF
  exact ⟨hF.filter_mono atTop_le_cocompact |>.tendsto,
    hF.filter_mono atBot_le_cocompact |>.tendsto⟩

/-- `∫ ∂ₓ f = 0` for `C¹` functions with compact support on `ℝ²`. -/
theorem integral_partialX_eq_zero {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    ∫ p, partialX f p = 0 := by
  have hcont : Continuous (partialX f) :=
    (contDiff_partialX (n := 0) (by simpa using hf)).continuous
  have hint : Integrable (partialX f) := hcont.integrable_of_hasCompactSupport
    (hs.of_isClosed_subset (isClosed_tsupport _) (tsupport_partialX_subset f))
  rw [Measure.volume_eq_prod, integral_prod_symm _ (by rwa [← Measure.volume_eq_prod])]
  have hline : ∀ y : ℝ, ∫ x, partialX f (x, y) = 0 := by
    intro y
    have hK : IsCompact (Prod.fst '' tsupport f) := hs.isCompact.image continuous_fst
    have hF : HasCompactSupport fun t ↦ f (t, y) := HasCompactSupport.intro hK fun t ht ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ ht ⟨(t, y), h, rfl⟩
    obtain ⟨htop, hbot⟩ := tendsto_zero_of_hasCompactSupport hF
    have hii : Integrable fun x ↦ partialX f (x, y) :=
      (hcont.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.intro hK fun t ht ↦ by
          change partialX f (t, y) = 0
          exact image_eq_zero_of_notMem_tsupport fun h ↦
            ht ⟨(t, y), tsupport_partialX_subset f h, rfl⟩)
    rw [integral_of_hasDerivAt_of_tendsto (fun x ↦ hasDerivAt_partialX (p := (x, y))
      (hf.differentiable one_ne_zero _)) hii hbot htop, sub_self]
  simp [hline]

/-- `∫ ∂_y f = 0` for `C¹` functions with compact support on `ℝ²`. -/
theorem integral_partialY_eq_zero {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    ∫ p, partialY f p = 0 := by
  have hcont : Continuous (partialY f) :=
    (contDiff_partialY (n := 0) (by simpa using hf)).continuous
  have hint : Integrable (partialY f) := hcont.integrable_of_hasCompactSupport
    (hs.of_isClosed_subset (isClosed_tsupport _) (tsupport_partialY_subset f))
  rw [Measure.volume_eq_prod, integral_prod _ (by rwa [← Measure.volume_eq_prod])]
  have hline : ∀ x : ℝ, ∫ y, partialY f (x, y) = 0 := by
    intro x
    have hK : IsCompact (Prod.snd '' tsupport f) := hs.isCompact.image continuous_snd
    have hF : HasCompactSupport fun t ↦ f (x, t) := HasCompactSupport.intro hK fun t ht ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ ht ⟨(x, t), h, rfl⟩
    obtain ⟨htop, hbot⟩ := tendsto_zero_of_hasCompactSupport hF
    have hii : Integrable fun y ↦ partialY f (x, y) :=
      (hcont.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
        (HasCompactSupport.intro hK fun t ht ↦ by
          change partialY f (x, t) = 0
          exact image_eq_zero_of_notMem_tsupport fun h ↦
            ht ⟨(x, t), tsupport_partialY_subset f h, rfl⟩)
    rw [integral_of_hasDerivAt_of_tendsto (fun y ↦ hasDerivAt_partialY (p := (x, y))
      (hf.differentiable one_ne_zero _)) hii hbot htop, sub_self]
  simp [hline]

/-- Integration by parts against a compactly supported function:
    `∫ u ∂ⱼφ = -∫ (∂ⱼu) φ`. -/
theorem integral_mul_coordPartial (j : Fin 2) (hu : ContDiff ℝ 1 u) (hφ : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) :
    ∫ p, u p * coordPartial j φ p = -∫ p, coordPartial j u p * φ p := by
  have hf : ContDiff ℝ 1 (fun p ↦ u p * φ p) := hu.mul hφ
  have hfs : HasCompactSupport (fun p ↦ u p * φ p) := hs.mul_left
  have hud := hu.differentiable one_ne_zero
  have hφd := hφ.differentiable one_ne_zero
  unfold coordPartial
  split_ifs
  · have hux := (contDiff_partialX (n := 0) (by simpa using hu)).continuous
    have hφx := (contDiff_partialX (n := 0) (by simpa using hφ)).continuous
    have h0 := integral_partialX_eq_zero hf hfs
    rw [show partialX (fun p ↦ u p * φ p) = fun p ↦ partialX u p * φ p + u p * partialX φ p
      from funext fun p ↦ partialX_mul (hud p) (hφd p)] at h0
    have i1 : Integrable fun p ↦ partialX u p * φ p :=
      (hux.mul hφ.continuous).integrable_of_hasCompactSupport hs.mul_left
    have i2 : Integrable fun p ↦ u p * partialX φ p := by
      have hφs : HasCompactSupport (partialX φ) :=
        hs.of_isClosed_subset (isClosed_tsupport _) (tsupport_partialX_subset φ)
      exact (hu.continuous.mul hφx).integrable_of_hasCompactSupport hφs.mul_left
    rw [integral_add i1 i2] at h0
    linear_combination h0
  · have huy := (contDiff_partialY (n := 0) (by simpa using hu)).continuous
    have hφy := (contDiff_partialY (n := 0) (by simpa using hφ)).continuous
    have h0 := integral_partialY_eq_zero hf hfs
    rw [show partialY (fun p ↦ u p * φ p) = fun p ↦ partialY u p * φ p + u p * partialY φ p
      from funext fun p ↦ partialY_mul (hud p) (hφd p)] at h0
    have i1 : Integrable fun p ↦ partialY u p * φ p :=
      (huy.mul hφ.continuous).integrable_of_hasCompactSupport hs.mul_left
    have i2 : Integrable fun p ↦ u p * partialY φ p := by
      have hφs : HasCompactSupport (partialY φ) :=
        hs.of_isClosed_subset (isClosed_tsupport _) (tsupport_partialY_subset φ)
      exact (hu.continuous.mul hφy).integrable_of_hasCompactSupport hφs.mul_left
    rw [integral_add i1 i2] at h0
    linear_combination h0

/-- Classical partial derivatives of a `C¹` function are weak partial derivatives on any `U`. -/
theorem hasWeakPartialOn_of_contDiff (hu : ContDiff ℝ 1 u) (U : Set (ℝ × ℝ)) (j : Fin 2) :
    HasWeakPartialOn U j u (coordPartial j u) :=
  ⟨hu.continuous.locallyIntegrable.locallyIntegrableOn U,
    (contDiff_coordPartial (n := 0) j (by simpa using hu)).continuous.locallyIntegrable
      |>.locallyIntegrableOn U,
    fun φ hφ ↦ integral_mul_coordPartial j hu (hφ.contDiff.of_le (by simp)) hφ.hasCompactSupport⟩

/-- A continuous function is square integrable on an open set with compact closure. -/
theorem memLp_two_restrict_of_continuous {f : ℝ × ℝ → ℂ} (hf : Continuous f) {V : Set (ℝ × ℝ)}
    (hVo : IsOpen V) (hV : IsCompact (closure V)) : MemLp f 2 (volume.restrict V) := by
  obtain ⟨C, hC⟩ := hV.exists_bound_of_continuousOn hf.continuousOn
  have hfin : volume V < ⊤ := (measure_mono subset_closure).trans_lt hV.measure_lt_top
  have : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.2 hfin.ne
  exact (memLp_top_of_bound hf.aestronglyMeasurable C
    (ae_restrict_of_forall_mem hVo.measurableSet fun x hx ↦ hC x (subset_closure hx))).mono_exponent
    le_top

/-- `Cᵏ` functions are in `Hᵏ_loc(U)`, with the classical derivatives as weak derivatives. -/
theorem memSobolevLocOn_of_contDiff (k : ℕ) (U : Set (ℝ × ℝ)) (hu : ContDiff ℝ k u) :
    MemSobolevLocOn k U u := by
  intro V hVo hV _
  induction k generalizing u with
  | zero => exact memLp_two_restrict_of_continuous hu.continuous hVo hV
  | succ k ih =>
    have hu1 : ContDiff ℝ 1 u := hu.of_le (by exact_mod_cast Nat.le_add_left 1 k)
    exact ⟨memLp_two_restrict_of_continuous hu.continuous hVo hV, fun j ↦
      ⟨coordPartial j u, hasWeakPartialOn_of_contDiff hu1 V j,
        ih (contDiff_coordPartial j (by exact_mod_cast hu))⟩⟩

end Classical

/-! ### Smooth cutoffs -/

section Cutoff

variable {U V : Set (ℝ × ℝ)} {g h χ : ℝ × ℝ → ℂ} {j : Fin 2}

theorem contDiff_coordPartial_top (j : Fin 2) {φ : ℝ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (coordPartial j φ) := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have h1 : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (m := ∞) (by simp)
  unfold coordPartial
  split_ifs
  · rw [show partialX φ = fun q ↦ fderiv ℝ φ q (1, 0) from
      funext fun q ↦ partialX_eq_fderiv (hd q)]
    exact h1.clm_apply contDiff_const
  · rw [show partialY φ = fun q ↦ fderiv ℝ φ q (0, 1) from
      funext fun q ↦ partialY_eq_fderiv (hd q)]
    exact h1.clm_apply contDiff_const

theorem coordPartial_mul (j : Fin 2) {a b : ℝ × ℝ → ℂ} (ha : Differentiable ℝ a)
    (hb : Differentiable ℝ b) :
    coordPartial j (fun p ↦ a p * b p) =
      fun p ↦ coordPartial j a p * b p + a p * coordPartial j b p := by
  funext p
  unfold coordPartial
  split_ifs
  · exact partialX_mul (ha p) (hb p)
  · exact partialY_mul (ha p) (hb p)

/-- Product rule for a smooth cutoff `χ` with compact support in `V`: if `h` is the weak
    derivative of `g` on `V`, then `(∂ⱼχ) g + χ h` is the weak derivative of `χ g` on any set
    `W`, since `χ φ` is a test function on `V` for every test function `φ`. -/
theorem HasWeakPartialOn.cutoff (hd : HasWeakPartialOn V j g h) (hχ : ContDiff ℝ ∞ χ)
    (hcs : HasCompactSupport χ) (hsub : tsupport χ ⊆ V) (W : Set (ℝ × ℝ)) :
    HasWeakPartialOn W j (fun p ↦ χ p * g p) (fun p ↦ coordPartial j χ p * g p + χ p * h p) := by
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hχc : Continuous χ := hχ.continuous
  have hχj : ContDiff ℝ ∞ (coordPartial j χ) := contDiff_coordPartial_top j hχ
  have hχjs : HasCompactSupport (coordPartial j χ) :=
    hcs.of_isClosed_subset (isClosed_tsupport _) (tsupport_coordPartial_subset j χ)
  have hχjsub : tsupport (coordPartial j χ) ⊆ V := (tsupport_coordPartial_subset j χ).trans hsub
  -- `χ g` and `(∂ⱼχ) g + χ h` are integrable on `ℝ²`.
  have ig : Integrable fun p ↦ g p * χ p := integrable_mul_of_tsupport_subset hd.1 hχc hcs hsub
  have ig' : Integrable fun p ↦ g p * coordPartial j χ p :=
    integrable_mul_of_tsupport_subset hd.1 hχj.continuous hχjs hχjsub
  have ih : Integrable fun p ↦ h p * χ p := integrable_mul_of_tsupport_subset hd.2.1 hχc hcs hsub
  have i1 : Integrable fun p ↦ χ p * g p := by simpa only [mul_comm] using ig
  have i2 : Integrable fun p ↦ coordPartial j χ p * g p + χ p * h p := by
    refine (ig'.add ih).congr (Eventually.of_forall fun p ↦ ?_)
    simp only [Pi.add_apply]
    ring
  refine ⟨i1.locallyIntegrable.locallyIntegrableOn W, i2.locallyIntegrable.locallyIntegrableOn W,
    fun φ hφ ↦ ?_⟩
  have hφd : Differentiable ℝ φ := hφ.contDiff.differentiable (by simp)
  -- `ψ = χ φ` is a test function on `V`.
  have hψ : IsTestFunctionOn V (fun p ↦ χ p * φ p) :=
    ⟨hχ.mul hφ.contDiff, hφ.hasCompactSupport.mul_left,
      (tsupport_mul_subset_left (f := χ) (g := φ)).trans hsub⟩
  have hw := hd.2.2 _ hψ
  rw [coordPartial_mul j hχd hφd] at hw
  have hφc := hφ.contDiff.continuous
  have hφj := hφ.continuous_coordPartial j
  have a1 : Integrable fun p ↦ g p * (coordPartial j χ p * φ p) :=
    integrable_mul_of_tsupport_subset hd.1 (hχj.continuous.mul hφc) hφ.hasCompactSupport.mul_left
      ((tsupport_mul_subset_left (f := coordPartial j χ) (g := φ)).trans hχjsub)
  have a2 : Integrable fun p ↦ g p * (χ p * coordPartial j φ p) :=
    integrable_mul_of_tsupport_subset hd.1 (hχc.mul hφj)
      (hφ.hasCompactSupport_coordPartial j).mul_left
      ((tsupport_mul_subset_left (f := χ) (g := coordPartial j φ)).trans hsub)
  have a3 : Integrable fun p ↦ h p * (χ p * φ p) :=
    integrable_mul_of_tsupport_subset hd.2.1 (hχc.mul hφc) hφ.hasCompactSupport.mul_left
      ((tsupport_mul_subset_left (f := χ) (g := φ)).trans hsub)
  simp only [mul_add] at hw
  rw [integral_add a1 a2] at hw
  have e1 : ∫ p, χ p * g p * coordPartial j φ p = ∫ p, g p * (χ p * coordPartial j φ p) := by
    congr 1; funext p; ring
  have e2 : ∫ p, (coordPartial j χ p * g p + χ p * h p) * φ p =
      (∫ p, g p * (coordPartial j χ p * φ p)) + ∫ p, h p * (χ p * φ p) := by
    rw [← integral_add a1 a3]
    congr 1; funext p; ring
  rw [e1, e2]
  linear_combination hw

/-- A cutoff of an `L²(V)` function, with the cutoff supported in `V`, is in `L²(ℝ²)`. -/
theorem memLp_cutoff {u : ℝ × ℝ → ℂ} (hVo : IsOpen V) (hu : MemLp u 2 (volume.restrict V))
    (hχc : Continuous χ) (hcs : HasCompactSupport χ) (hsub : tsupport χ ⊆ V) :
    MemLp (fun p ↦ χ p * u p) 2 volume := by
  obtain ⟨C, hC⟩ := hχc.bounded_above_of_compact_support hcs
  have hχ : MemLp χ ⊤ (volume.restrict V) :=
    memLp_top_of_bound hχc.aestronglyMeasurable C (Eventually.of_forall hC)
  have hV : MemLp (fun p ↦ χ p * u p) 2 (volume.restrict V) := by
    simpa only [Pi.mul_def] using hχ.mul hu
  have hind : (fun p ↦ χ p * u p) = V.indicator (fun p ↦ χ p * u p) := by
    funext p
    by_cases hp : p ∈ V
    · simp [hp]
    · have : χ p = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hp (hsub h)
      simp [hp, this]
  rw [hind, memLp_indicator_iff_restrict hVo.measurableSet]
  exact hV

/-- Localization: if `u ∈ Hᵏ_loc(U)` and `χ` is smooth with compact support in `U`, then
    `χ u ∈ Hᵏ(ℝ²)`, with weak derivatives given by the product rule. -/
theorem MemSobolevLocOn.cutoff (k : ℕ) {u : ℝ × ℝ → ℂ} (hU : IsOpen U)
    (hu : MemSobolevLocOn k U u) (hχ : ContDiff ℝ ∞ χ) (hcs : HasCompactSupport χ)
    (hsub : tsupport χ ⊆ U) : MemSobolevOn k univ (fun p ↦ χ p * u p) := by
  induction k generalizing U u χ with
  | zero =>
    obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hcs hU hsub
    have huV : MemSobolevOn 0 V u := hu V hVo hVc hVU
    change MemLp _ 2 (volume.restrict univ)
    rw [Measure.restrict_univ]
    exact memLp_cutoff hVo huV hχ.continuous hcs hKV
  | succ k ih =>
    obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hcs hU hsub
    have huV : MemSobolevOn (k + 1) V u := hu V hVo hVc hVU
    refine ⟨?_, fun j ↦ ?_⟩
    · rw [Measure.restrict_univ]
      exact memLp_cutoff hVo huV.1 hχ.continuous hcs hKV
    · obtain ⟨d, hd, hdk⟩ := huV.2 j
      have hχjs : HasCompactSupport (coordPartial j χ) :=
        hcs.of_isClosed_subset (isClosed_tsupport _) (tsupport_coordPartial_subset j χ)
      refine ⟨_, hd.cutoff hχ hcs hKV univ, MemSobolevOnWith.add ?_ ?_⟩
      · exact ih hVo (MemSobolevOn.memSobolevLocOn (MemSobolevOnWith.of_succ huV))
          (contDiff_coordPartial_top j hχ) hχjs ((tsupport_coordPartial_subset j χ).trans hKV)
      · exact ih hVo (MemSobolevOn.memSobolevLocOn hdk) hχ hcs hKV

end Cutoff

/-- Changing the left function on a null set preserves weak derivatives. -/
theorem HasWeakPartialOn.congr_left {U : Set (ℝ × ℝ)} {j : Fin 2} {g g' h : ℝ × ℝ → ℂ}
    (hgh : HasWeakPartialOn U j g h) (hg : g =ᵐ[volume] g') : HasWeakPartialOn U j g' h := by
  refine ⟨hgh.1.congr (ae_restrict_of_ae hg), hgh.2.1, fun φ hφ ↦ ?_⟩
  rw [← hgh.2.2 φ hφ]
  exact integral_congr_ae (hg.mono fun p hp ↦ by simp [hp])

/-- Changing a function on a null set preserves local Sobolev membership. -/
theorem MemSobolevOn.congr_ae {k : ℕ} {U : Set (ℝ × ℝ)} {g g' : ℝ × ℝ → ℂ}
    (h : MemSobolevOn k U g) (hg : g =ᵐ[volume] g') : MemSobolevOn k U g' := by
  cases k with
  | zero => exact MemLp.ae_eq (ae_restrict_of_ae hg) h
  | succ k =>
    obtain ⟨hL, hd⟩ := h
    refine ⟨MemLp.ae_eq (ae_restrict_of_ae hg) hL, fun j ↦ ?_⟩
    obtain ⟨d, hd1, hd2⟩ := hd j
    exact ⟨d, hd1.congr_left hg, hd2⟩

/-- Changing a function a.e. on its domain preserves Sobolev membership.
No agreement outside the domain is required. -/
theorem MemSobolevOn.congr_ae_on {k : ℕ} {U : Set (ℝ × ℝ)} {g g' : ℝ × ℝ → ℂ}
    (h : MemSobolevOn k U g) (hU : MeasurableSet U)
    (hg : ∀ᵐ p, p ∈ U → g p = g' p) : MemSobolevOn k U g' := by
  cases k with
  | zero => exact MemLp.ae_eq ((ae_restrict_iff' hU).mpr hg) h
  | succ k =>
    refine ⟨MemLp.ae_eq ((ae_restrict_iff' hU).mpr hg) h.1, fun j ↦ ?_⟩
    obtain ⟨d, hd, hdk⟩ := h.2 j
    exact ⟨d, hd.congr_ae_on hU hg (Filter.Eventually.of_forall fun _ _ ↦ rfl), hdk⟩

/-- Local Sobolev membership depends only on a.e. values on the domain.
The domain itself need not be measurable. -/
theorem MemSobolevLocOn.congr_ae_on {k : ℕ} {U : Set (ℝ × ℝ)} {g g' : ℝ × ℝ → ℂ}
    (h : MemSobolevLocOn k U g) (hg : ∀ᵐ p, p ∈ U → g p = g' p) :
    MemSobolevLocOn k U g' := by
  intro V hV hc hVU
  apply (h V hV hc hVU).congr_ae_on hV.measurableSet
  filter_upwards [hg] with p hp hpV
  exact hp (hVU (subset_closure hpV))

/-! ### From the lift to the torus

The periodization of cut-off local functions (`lem:local-to-global`) is in
`LocalToGlobal.lean`; the converse direction, lifts of torus Sobolev functions, is in
`LiftPeriodization.lean`. -/

/-! ### Traces on lines in diagonal coordinates

ACL representatives, elementary L² traces, H² trace differentiation and the fractional
trace bound are proved in `DiagonalACL.lean`, `TraceL2.lean`, `TraceH2.lean` and
`TraceGagliardo.lean`, respectively. -/

section Traces

/-- The diagonal rectangle `{a ∈ I, b ∈ J}` in diagonal coordinates `a = (x+y)/2`,
    `b = (x-y)/2`. -/
def diagRect (I J : Set ℝ) : Set (ℝ × ℝ) := {p | (diagCoord p).1 ∈ I ∧ (diagCoord p).2 ∈ J}

end Traces

end NoEmbeddedEigenvalues
