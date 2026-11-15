import NoEmbeddedEigenvalues.QuarterScalars
import NoEmbeddedEigenvalues.PeriodDerivativeBounds
import NoEmbeddedEigenvalues.OrbitCoordinates
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Geometry of quarter-divisor resonances

Blueprint: `lem:quarter-divisor-geometry`.

The positive phase uses the absolute spectral parameter. Its resonances are an
arithmetic lattice in phase, not in physical level. Logarithmic derivative bounds
convert fixed phase increments into uniform level ratios. Jordan's sine inequality
then controls the divisor throughout each complete phase cell.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open Set Filter
open scoped Topology

private theorem logarithmic_comparison {F : ℝ → ℝ} {c C r : ℝ}
    (hd : ∀ x ∈ Ioo 0 r, DifferentiableAt ℝ F x)
    (hb : ∀ x ∈ Ioo 0 r, c ≤ -x * deriv F x ∧ -x * deriv F x ≤ C)
    {x y : ℝ} (hx : x ∈ Ioo 0 r) (hy : y ∈ Ioo 0 r) (hxy : x ≤ y) :
    c * Real.log (y / x) ≤ F x - F y ∧
      F x - F y ≤ C * Real.log (y / x) := by
  have hder (A : ℝ) (z : ℝ) (hz : z ∈ Ioo 0 r) :
      HasDerivAt (fun z ↦ F z + A * Real.log z) (deriv F z + A / z) z := by
    convert (hd z hz).hasDerivAt.add ((Real.hasDerivAt_log hz.1.ne').const_mul A) using 1
    simp [div_eq_mul_inv]
  have hlo : AntitoneOn (fun z ↦ F z + c * Real.log z) (Ioo 0 r) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioo _ _)
    · exact fun z hz ↦ (hder c z hz).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Ioo] at hz
      exact (hder c z hz).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Ioo] at hz
      rw [(hder c z hz).deriv]
      have hq : c / z ≤ -deriv F z :=
        (div_le_iff₀ hz.1).2 (by nlinarith [(hb z hz).1])
      linarith
  have hhi : MonotoneOn (fun z ↦ F z + C * Real.log z) (Ioo 0 r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo _ _)
    · exact fun z hz ↦ (hder C z hz).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Ioo] at hz
      exact (hder C z hz).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Ioo] at hz
      rw [(hder C z hz).deriv]
      have := (hb z hz).2
      have hq : -deriv F z ≤ C / z := (le_div_iff₀ hz.1).2 (by nlinarith)
      linarith
  rw [Real.log_div hy.1.ne' hx.1.ne']
  exact ⟨by linarith [hlo hx hy hxy], by linarith [hhi hx hy hxy]⟩

private theorem logarithmic_ratio_bounds {F : ℝ → ℝ} {c C r T x y : ℝ}
    (hc : 0 < c) (hC : 0 < C)
    (hd : ∀ x ∈ Ioo 0 r, DifferentiableAt ℝ F x)
    (hb : ∀ x ∈ Ioo 0 r, c ≤ -x * deriv F x ∧ -x * deriv F x ≤ C)
    (hx : x ∈ Ioo 0 r) (hy : y ∈ Ioo 0 r) (hxy : x ≤ y) (hT : F x - F y = T) :
    Real.exp (-T / c) ≤ x / y ∧ x / y ≤ Real.exp (-T / C) := by
  obtain ⟨hl, hu⟩ := logarithmic_comparison hd hb hx hy hxy
  rw [hT, Real.log_div hy.1.ne' hx.1.ne'] at hl hu
  constructor
  · apply (Real.le_log_iff_exp_le (div_pos hx.1 hy.1)).1
    rw [Real.log_div hx.1.ne' hy.1.ne']
    have := (le_div_iff₀ hc).2 (by linarith : (Real.log y - Real.log x) * c ≤ T)
    rw [neg_div]
    linarith
  · apply (Real.log_le_iff_le_exp (div_pos hx.1 hy.1)).1
    rw [Real.log_div hx.1.ne' hy.1.ne']
    have := (div_le_iff₀ hC).2 (by linarith : T ≤ (Real.log y - Real.log x) * C)
    rw [neg_div]
    linarith

private theorem phase_lattice_enumeration {F : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn F (Ioo 0 r)) (ha : StrictAntiOn F (Ioo 0 r))
    (htop : Tendsto F (𝓝[>] 0) atTop) (θ : ℝ) {T : ℝ} (hT : 0 < T) :
    ∃ ρ : ℝ, ρ ∈ Ioo 0 r ∧ ∃ hs : ℕ → ℝ,
      (∀ n, hs n ∈ Ioo 0 ρ ∧ (∃ k : ℤ, F (hs n) = θ + k * T) ∧
        F (hs (n + 1)) - F (hs n) = T) ∧
      (∀ h ∈ Ioo 0 ρ, (∃ k : ℤ, F h = θ + k * T) ↔ ∃ n, h = hs n) := by
  have hsolve {δ t : ℝ} (hδ : δ ∈ Ioo 0 r) (ht : F δ < t) :
      ∃ x ∈ Ioo 0 δ, F x = t := by
    have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo 0 δ ∧ t < F x := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hδ.1).filter_mono nhdsWithin_le_nhds,
        htop.eventually (eventually_gt_atTop t)] with x hx hxδ hxt
      exact ⟨⟨hx, hxδ⟩, hxt⟩
    obtain ⟨x, hx, hxt⟩ := hev.exists
    obtain ⟨y, hy, hyt⟩ := intermediate_value_Ioo' hx.2.le
      (hc.mono (Icc_subset_Ioo hx.1 hδ.2)) ⟨ht, hxt⟩
    exact ⟨y, ⟨hx.1.trans hy.1, hy.2⟩, hyt⟩
  let δ := r / 2
  have hδ : δ ∈ Ioo 0 r := ⟨by dsimp [δ]; linarith, by dsimp [δ]; linarith⟩
  obtain ⟨m, hm⟩ := exists_int_gt ((F δ - θ + T) / T)
  have hm' := (div_lt_iff₀ hT).1 hm
  obtain ⟨ρ, hρ, hρeq⟩ := hsolve hδ
    (show F δ < θ + (m : ℝ) * T - T / 2 by linarith)
  have hρr : ρ ∈ Ioo 0 r := ⟨hρ.1, hρ.2.trans hδ.2⟩
  have hex (n : ℕ) : ∃ x ∈ Ioo 0 ρ, F x = θ + ((m : ℝ) + n) * T := by
    apply hsolve hρr
    rw [hρeq]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  choose hs hhs heq using hex
  refine ⟨ρ, hρr, hs, ?_, ?_⟩
  · intro n
    refine ⟨hhs n, ⟨m + n, ?_⟩, ?_⟩
    · simpa only [Int.cast_add, Int.cast_natCast] using heq n
    · rw [heq, heq, Nat.cast_add, Nat.cast_one]
      ring
  · intro h hh
    constructor
    · rintro ⟨k, hk⟩
      have hlt := ha ⟨hh.1, hh.2.trans hρr.2⟩ hρr hh.2
      rw [hk, hρeq] at hlt
      have hmk : m ≤ k := by
        by_contra h
        have hkm : (k : ℝ) + 1 ≤ m := by exact_mod_cast (show k + 1 ≤ m by omega)
        nlinarith
      refine ⟨(k - m).toNat, ?_⟩
      apply ha.injOn ⟨hh.1, hh.2.trans hρr.2⟩
        ⟨(hhs _).1, (hhs _).2.trans hρr.2⟩
      rw [hk, heq]
      have hn : ((k - m).toNat : ℝ) = (k : ℝ) - m := by
        exact_mod_cast (Int.toNat_of_nonneg (sub_nonneg.2 hmk))
      rw [hn]
      ring
    · rintro ⟨n, rfl⟩
      exact ⟨m + n, by simpa only [Int.cast_add, Int.cast_natCast] using heq n⟩

private theorem exp_I_eq_iff {x y : ℝ} :
    Complex.exp (Complex.I * (x : ℂ)) = Complex.exp (Complex.I * (y : ℂ)) ↔
      ∃ k : ℤ, x = y + k * (2 * Real.pi) := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa using congrArg Complex.im hk
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    push_cast
    ring

private theorem positive_phase_lattice {lam : ℝ} (hlam : lam ≠ 0)
    {κ : ℂ} (hκ : κ ^ 4 = 1) : ∃ θ : ℝ, ∀ h : ℝ,
      quarterDivisor lam κ h = 0 ↔
        ∃ k : ℤ, quarterPhase |lam| h = θ + k * (2 * Real.pi) := by
  have hn : ‖κ‖ = 1 := by
    have := congrArg norm hκ
    simpa only [norm_pow, norm_one, pow_eq_one_iff_of_nonneg (norm_nonneg κ)
      (by norm_num : (4 : ℕ) ≠ 0)] using this
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff κ).1 hn
  have hθ' : Complex.exp (Complex.I * (θ : ℂ)) = κ := by simpa only [mul_comm] using hθ
  by_cases hl : 0 < lam
  · refine ⟨θ, ?_⟩
    intro h
    rw [quarterDivisor, sub_eq_zero, ← hθ', eq_comm, exp_I_eq_iff,
      abs_of_pos hl]
  · have hl' : lam < 0 := lt_of_le_of_ne (le_of_not_gt hl) hlam
    refine ⟨-θ, ?_⟩
    intro h
    have hp : quarterPhase lam h = -quarterPhase |lam| h := by
      simp only [quarterPhase, abs_of_neg hl']; ring
    rw [quarterDivisor, sub_eq_zero, ← hθ', eq_comm, hp]
    have he : Complex.exp (Complex.I * ((-quarterPhase |lam| h : ℝ) : ℂ)) =
        Complex.exp (Complex.I * (θ : ℂ)) ↔
        Complex.exp (Complex.I * (quarterPhase |lam| h : ℂ)) =
          Complex.exp (Complex.I * ((-θ : ℝ) : ℂ)) := by
      simp only [Complex.ofReal_neg, mul_neg, Complex.exp_neg]
      exact inv_eq_iff_eq_inv
    rw [he, exp_I_eq_iff]

private theorem quarterDivisor_deriv_ne_zero {lam : ℝ} (hlam : lam ≠ 0)
    (κ : ℂ) {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    deriv (quarterDivisor lam κ) h ≠ 0 := by
  obtain ⟨hd, hn⟩ := deriv_eighthPeriod_neg h0 h1
  have hp := hd.hasDerivAt.const_mul (2 * lam)
  have hdv := (hasDerivAt_const h κ).sub
    (((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt h hp).const_mul Complex.I).cexp)
  change HasDerivAt (quarterDivisor lam κ) _ h at hdv
  rw [hdv.deriv]
  simp only [zero_sub, neg_ne_zero, Complex.ofRealCLM_apply]
  exact mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero Complex.I_ne_zero
    (Complex.ofReal_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) hlam) hn.ne)))

theorem phase_chord_lower {x y : ℝ} (hxy : |x - y| ≤ Real.pi) :
    (2 / Real.pi) * |x - y| ≤
      ‖Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ))‖ := by
  have he : Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ)) =
      Complex.exp (Complex.I * (y : ℂ)) *
        (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, zero_mul, sub_self, Real.exp_zero, one_mul]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hs := Real.mul_abs_le_abs_sin (x := (x - y) / 2)
    (by simpa only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      (div_le_div_of_nonneg_right hxy (by norm_num : (0 : ℝ) ≤ 2)))
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hs
  linarith

theorem logarithmic_cell_geometry {F : ℝ → ℝ} {c C r : ℝ} (hc : 0 < c)
    (ha : AntitoneOn F (Ioo 0 r))
    (hd : ∀ x ∈ Ioo 0 r, DifferentiableAt ℝ F x)
    (hb : ∀ x ∈ Ioo 0 r, c ≤ -x * deriv F x ∧ -x * deriv F x ≤ C) :
    ∃ K : ℝ, 1 < K ∧ ∀ z ∈ Ioo 0 r, ∀ h ∈ Ioo 0 r,
      |F h - F z| ≤ Real.pi → z / K ≤ h ∧ h ≤ K * z ∧
        |h - z| / (K * z) ≤ (2 / Real.pi) * |F h - F z| := by
  let B := Real.exp (Real.pi / c)
  have hB : 0 < B := Real.exp_pos _
  have hB1 : 1 ≤ B := Real.one_le_exp (by positivity)
  have hordered {x y : ℝ} (hx : x ∈ Ioo 0 r) (hy : y ∈ Ioo 0 r)
      (hxy : x ≤ y) (hphase : F x - F y ≤ Real.pi) :
      y ≤ B * x ∧ c * (y - x) ≤ y * (F x - F y) := by
    have hl := (logarithmic_comparison hd hb hx hy hxy).1
    have hl' : Real.log (y / x) ≤ Real.pi / c :=
      (le_div_iff₀ hc).2 (by nlinarith)
    have hratio := (Real.log_le_iff_le_exp (div_pos hy.1 hx.1)).1 hl'
    have hlinear := Real.one_sub_inv_le_log_of_pos (div_pos hy.1 hx.1)
    rw [inv_div] at hlinear
    have hm := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left hlinear hc.le).trans hl) hy.1.le
    have he : y * (c * (1 - x / y)) = c * (y - x) := by
      field_simp [hy.1.ne']
    rw [he] at hm
    exact ⟨(div_le_iff₀ hx.1).1 hratio, hm⟩
  let K := max (B + 1) (Real.pi * B / (2 * c) + 1)
  have hK : 1 < K := (by linarith : 1 < B + 1).trans_le (le_max_left _ _)
  have hBK : B ≤ K := (by linarith : B ≤ B + 1).trans (le_max_left _ _)
  have hcoef : Real.pi * B ≤ 2 * c * K := by
    rw [mul_comm (2 * c) K]
    apply (div_le_iff₀ (by positivity : 0 < 2 * c)).1
    exact (le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)
  refine ⟨K, hK, ?_⟩
  intro z hz h hh hp
  have hK0 : 0 < K := zero_lt_one.trans hK
  have hcomp : h ≤ B * z ∧ z ≤ B * h ∧
      c * |h - z| ≤ B * z * |F h - F z| := by
    rcases le_total h z with hhz | hzh
    · have ha' := ha hh hz hhz
      have habs : |F h - F z| = F h - F z := abs_of_nonneg (sub_nonneg.2 ha')
      obtain ⟨hzb, hlin⟩ := hordered hh hz hhz (by rwa [habs] at hp)
      rw [abs_of_nonpos (sub_nonpos.2 hhz), habs]
      refine ⟨?_, hzb, ?_⟩
      · exact hhz.trans (le_mul_of_one_le_left hz.1.le hB1)
      · exact (by nlinarith : c * -(h - z) ≤ z * (F h - F z)).trans
          (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hz.1.le hB1)
            (sub_nonneg.2 ha'))
    · have ha' := ha hz hh hzh
      have habs : |F h - F z| = F z - F h := by
        rw [abs_of_nonpos (sub_nonpos.2 ha')]; ring
      obtain ⟨hhb, hlin⟩ := hordered hz hh hzh (by rwa [habs] at hp)
      rw [abs_of_nonneg (sub_nonneg.2 hzh), habs]
      refine ⟨hhb, ?_, hlin.trans (mul_le_mul_of_nonneg_right hhb (sub_nonneg.2 ha'))⟩
      exact hzh.trans (le_mul_of_one_le_left hh.1.le hB1)
  refine ⟨(div_le_iff₀ hK0).2 (hcomp.2.1.trans (by nlinarith [hh.1])),
    hcomp.1.trans (by nlinarith [hz.1]), ?_⟩
  apply (div_le_iff₀ (mul_pos hK0 hz.1)).2
  apply le_of_mul_le_mul_left (a := Real.pi * c) _ (mul_pos Real.pi_pos hc)
  have he : (Real.pi * c) * ((2 / Real.pi) * |F h - F z| * (K * z)) =
      (2 * c * K) * (z * |F h - F z|) := by
    field_simp
  rw [he]
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left hcomp.2.2 Real.pi_pos.le).trans
      (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg hz.1.le (abs_nonneg (F h - F z))))

/-- Simple resonances, geometric ratio bounds and uniform full-cell comparisons.
The cutoff can be chosen arbitrarily small; no exact geometric progression is claimed. -/
theorem quarter_divisor_geometry {lam : ℝ} (hlam : lam ≠ 0) {κ : ℂ} (hκ : κ ^ 4 = 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ ρ K qlower qupper : ℝ, 0 < ρ ∧ ρ < η ∧ ρ < 1 ∧ 1 < K ∧
      0 < qlower ∧ qlower ≤ qupper ∧ qupper < 1 ∧
      (∀ h ∈ Ioo 0 ρ, quarterDivisor lam κ h = 0 → deriv (quarterDivisor lam κ) h ≠ 0) ∧
      (∃ hs : ℕ → ℝ,
        (∀ n, hs n ∈ Ioo 0 ρ ∧ quarterDivisor lam κ (hs n) = 0 ∧
          qlower ≤ hs (n + 1) / hs n ∧ hs (n + 1) / hs n ≤ qupper) ∧
        (∀ h ∈ Ioo 0 ρ, quarterDivisor lam κ h = 0 ↔ ∃ n, h = hs n)) ∧
      (∀ z ∈ Ioo 0 ρ, quarterDivisor lam κ z = 0 → ∀ h ∈ Ioo 0 ρ,
        |quarterPhase lam h - quarterPhase lam z| ≤ Real.pi →
          z / K ≤ h ∧ h ≤ K * z ∧ |h - z| / (K * z) ≤ ‖quarterDivisor lam κ h‖) := by
  obtain ⟨c, C, r, hc, hC, hr, hr1, hb⟩ := eighthPeriod_derivative_bounds
  let δ := min r η / 2
  have hδ : 0 < δ := half_pos (lt_min hr hη)
  have hδr : δ < r := by have := min_le_left r η; dsimp [δ]; linarith
  have hδη : δ < η := by have := min_le_right r η; dsimp [δ]; linarith
  have hδ1 : δ < 1 := hδr.trans hr1
  let A := 2 * |lam|
  have hA : 0 < A := mul_pos (by norm_num) (abs_pos.2 hlam)
  let P := quarterPhase |lam|
  have hder (h : ℝ) (hh : h ∈ Ioo 0 δ) : HasDerivAt P (A * deriv eighthPeriod h) h :=
    (deriv_eighthPeriod_neg hh.1 (hh.2.trans hδ1)).1.hasDerivAt.const_mul A
  have hPc : ContinuousOn P (Ioo 0 δ) := fun h hh ↦
    (hder h hh).continuousAt.continuousWithinAt
  have hPa : StrictAntiOn P (Ioo 0 δ) := by
    intro x hx y hy hxy
    exact mul_lt_mul_of_pos_left
      (eighthPeriod_strictAntiOn ⟨hx.1, hx.2.trans hδ1⟩ ⟨hy.1, hy.2.trans hδ1⟩ hxy) hA
  have hPtop : Tendsto P (𝓝[>] 0) atTop := tendsto_eighthPeriod_atTop.const_mul_atTop hA
  have hPb (h : ℝ) (hh : h ∈ Ioo 0 δ) :
      A * c ≤ -h * deriv P h ∧ -h * deriv P h ≤ A * C := by
    rw [(hder h hh).deriv]
    obtain ⟨hl, hu, -⟩ := hb h ⟨hh.1, hh.2.trans hδr⟩
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hl hA.le,
      mul_le_mul_of_nonneg_left hu hA.le]
  obtain ⟨θ, hθ⟩ := positive_phase_lattice hlam hκ
  obtain ⟨ρ, hρ, hs, hhs, hcover⟩ := phase_lattice_enumeration hδ hPc hPa hPtop θ
    (by positivity : 0 < 2 * Real.pi)
  have hsub : Ioo 0 ρ ⊆ Ioo 0 δ := Ioo_subset_Ioo le_rfl hρ.2.le
  have hlevels (n : ℕ) : hs n ∈ Ioo 0 δ := hsub (hhs n).1
  have hdec (n : ℕ) : hs (n + 1) < hs n := by
    by_contra hn
    have := hPa.antitoneOn (hlevels n) (hlevels (n + 1)) (le_of_not_gt hn)
    linarith [(hhs n).2.2, Real.pi_pos]
  have hrat (n : ℕ) := logarithmic_ratio_bounds (mul_pos hA hc) (mul_pos hA hC)
    (fun h hh ↦ (hder h hh).differentiableAt) hPb (hlevels (n + 1)) (hlevels n)
    (hdec n).le (hhs n).2.2
  obtain ⟨K, hK, hcell⟩ := logarithmic_cell_geometry (mul_pos hA hc) hPa.antitoneOn
    (fun h hh ↦ (hder h hh).differentiableAt) hPb
  refine ⟨ρ, K, Real.exp (-(2 * Real.pi) / (A * c)),
    Real.exp (-(2 * Real.pi) / (A * C)), hρ.1, hρ.2.trans hδη,
    hρ.2.trans hδ1, hK, Real.exp_pos _, (hrat 0).1.trans (hrat 0).2, ?_, ?_, ?_, ?_⟩
  · apply Real.exp_lt_one_iff.2
    exact div_neg_of_neg_of_pos (by linarith [Real.pi_pos]) (mul_pos hA hC)
  · intro h hh _
    exact quarterDivisor_deriv_ne_zero hlam κ hh.1 (hh.2.trans (hρ.2.trans hδ1))
  · refine ⟨hs, fun n ↦ ⟨(hhs n).1, (hθ _).2 (hhs n).2.1, hrat n⟩, ?_⟩
    intro h hh
    exact (hθ h).trans (hcover h hh)
  · intro z hz hzero h hh hphase
    have habs : |P h - P z| = |quarterPhase lam h - quarterPhase lam z| := by
      dsimp only [P, quarterPhase]
      rw [← mul_sub, ← mul_sub]
      simp only [abs_mul, abs_abs]
    obtain ⟨hl, hu, hd⟩ := hcell z (hsub hz) h (hsub hh) (by rwa [habs])
    refine ⟨hl, hu, hd.trans ?_⟩
    rw [habs, quarterDivisor, (sub_eq_zero.1 hzero), norm_sub_rev]
    exact phase_chord_lower hphase

end NoEmbeddedEigenvalues
