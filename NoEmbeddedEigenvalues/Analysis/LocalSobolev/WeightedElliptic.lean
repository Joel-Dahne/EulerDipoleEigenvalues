module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.QuotientLocal
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.WeakJetOperations

/-!
# Radially weighted interior elliptic regularity

The weighted third-order gain is the dyadic summation corollary of the uniform
annular estimate. It is an analytic input, independent of eigenfunctions or parity.
Lower jet entries are preserved, not replaced by unrelated representatives.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- Using ratio 2/3 makes the open inner annuli cover even their neighbors' boundary
circles. After six steps the radius has shrunk by more than a factor of eight. -/
private def shellRadius (σ : ℝ) (n : ℕ) : ℝ := σ * (2 / 3 : ℝ) ^ n

private theorem shellRadius_pos {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    0 < shellRadius σ n := by
  unfold shellRadius
  positivity

private theorem shellRadius_succ (σ : ℝ) (n : ℕ) :
    shellRadius σ (n + 1) = shellRadius σ n * (2 / 3) := by
  unfold shellRadius
  rw [pow_succ, mul_assoc]

private theorem shellRadius_antitone {σ : ℝ} (hσ : 0 < σ) : Antitone (shellRadius σ) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [shellRadius_succ]
  linarith [shellRadius_pos hσ n]

private theorem shell_cover {σ : ℝ} (hσ : 0 < σ) (c : ℝ × ℝ) :
    localDisk c σ \ {c} ⊆
      ⋃ n, ellipticAnnulus c (shellRadius σ n) (2 * shellRadius σ n) := by
  intro p hp
  have ht : 0 < localRadius c p :=
    lt_of_le_of_ne (Real.sqrt_nonneg _) (localRadius_ne_zero hp.2).symm
  have hlim : Tendsto (shellRadius σ) atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ ↦ σ * (2 / 3 : ℝ) ^ n) atTop (𝓝 0)
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
        (by norm_num)).const_mul σ
  have hex : ∃ n, shellRadius σ n < localRadius c p :=
    (hlim.eventually (gt_mem_nhds ht)).exists
  refine mem_iUnion.2 ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  generalize hn : Nat.find hex = n
  cases n with
  | zero =>
    have h : localRadius c p < σ := hp.1
    simp only [shellRadius, pow_zero, mul_one]
    linarith
  | succ n =>
    have h : localRadius c p ≤ shellRadius σ n :=
      le_of_not_gt (Nat.find_min hex (by omega))
    rw [shellRadius_succ]
    linarith only [h, shellRadius_pos hσ n]

private theorem shell_overlap {σ : ℝ} (hσ : 0 < σ) (c : ℝ × ℝ) (j : Fin 6) :
    Pairwise fun m n ↦ Disjoint
      (ellipticAnnulus c (shellRadius σ (m * 6 + j) / 2) (4 * shellRadius σ (m * 6 + j)))
      (ellipticAnnulus c (shellRadius σ (n * 6 + j) / 2) (4 * shellRadius σ (n * 6 + j))) := by
  let B (n : ℕ) := ellipticAnnulus c (shellRadius σ (n * 6 + j) / 2)
    (4 * shellRadius σ (n * 6 + j))
  have hlt (m n : ℕ) (hmn : m < n) : Disjoint (B m) (B n) := by
    have hi : m * 6 + j.val + 6 ≤ n * 6 + j.val := by omega
    have h := shellRadius_antitone hσ hi
    have hpow (k : ℕ) : shellRadius σ (k + 6) = shellRadius σ k * (2 / 3 : ℝ) ^ 6 := by
      unfold shellRadius
      rw [pow_add, mul_assoc]
    rw [hpow] at h
    have hcoef : 4 * (2 / 3 : ℝ) ^ 6 ≤ 1 / 2 := by norm_num
    have hr := shellRadius_pos hσ (m * 6 + j.val)
    apply disjoint_left.mpr
    rintro p ⟨hp, -⟩ ⟨-, hq⟩
    have hsep : 4 * shellRadius σ (n * 6 + j.val) ≤ shellRadius σ (m * 6 + j.val) / 2 := by
      nlinarith only [h, mul_le_mul_of_nonneg_right hcoef hr.le]
    exact (not_lt_of_ge hsep) (hp.trans hq)
  intro m n hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hlt m n h
  · exact (hlt n m h).symm

/-- Summing the real energy bounds is legitimate only after passing to nonnegative
integrals on the individual patches. Grouping the outer patches by residue gives
a finite sum of integrals over disjoint families. -/
private theorem memLp_of_shell_bounds {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A B : ℕ → Set α} {U : Set α} (hB : ∀ n, MeasurableSet (B n))
    (hBU : ∀ n, B n ⊆ U)
    (hdis : ∀ j : Fin 6, Pairwise fun m n ↦ Disjoint (B (m * 6 + j)) (B (n * 6 + j)))
    {f : α → ℂ} {H : α → ℝ} {K : ℝ} (hK : 0 ≤ K) (hH : IntegrableOn H U μ)
    (hpos : ∀ p, 0 ≤ H p) (hf : ∀ n, MemLp f 2 (μ.restrict (A n)))
    (hbound : ∀ n, (∫ p in A n, ‖f p‖ ^ 2 ∂μ) ≤ K * ∫ p in B n, H p ∂μ) :
    MemLp f 2 (μ.restrict (⋃ n, A n)) := by
  let b (n : ℕ) := ∫⁻ p in B n, ENNReal.ofReal (H p) ∂μ
  have hb : ∑' n, b n < ∞ := by
    rw [← (Nat.divModEquiv 6).symm.tsum_eq b, tsum_prod', tsum_comm,
      tsum_fintype]
    apply ENNReal.sum_lt_top.mpr
    intro j _
    simp only [Nat.divModEquiv_symm_apply, b]
    rw [← lintegral_iUnion (fun n ↦ hB (n * 6 + j)) (hdis j)]
    exact (lintegral_mono_set (iUnion_subset fun n ↦ hBU (n * 6 + j))).trans_lt
      hH.lintegral_lt_top
  have hfm := AEStronglyMeasurable.iUnion fun n ↦ (hf n).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hfm).2
  refine ⟨hfm.norm.pow 2, (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall fun _ ↦ sq_nonneg _)).2 ?_⟩
  have he (n : ℕ) : (∫⁻ p in A n, ENNReal.ofReal (‖f p‖ ^ 2) ∂μ) ≤ ENNReal.ofReal K * b n := by
    rw [← ofReal_integral_eq_lintegral_ofReal ((hf n).integrable_norm_pow (by decide))
      (Eventually.of_forall fun _ ↦ sq_nonneg _)]
    dsimp only [b]
    rw [← ofReal_integral_eq_lintegral_ofReal (hH.mono_set (hBU n))
      (Eventually.of_forall hpos), ← ENNReal.ofReal_mul hK]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  exact (lintegral_iUnion_le A _).trans_lt ((tsum_le_tsum he).trans_lt (by
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hb))

private def weightedDensity (c : ℝ × ℝ) (s : ℕ) (f : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ‖f p / (localRadius c p ^ s : ℂ)‖ ^ 2

private theorem radial_norm_factor (c p : ℝ × ℝ) (s : ℕ) (z : ℂ)
    (hp : 0 < localRadius c p) :
    ‖z‖ = localRadius c p ^ s * ‖z / (localRadius c p ^ s : ℂ)‖ := by
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  exact (mul_div_cancel₀ _ (pow_ne_zero s hp.ne')).symm

private theorem weighted_outer_energy {c : ℝ × ℝ} {r : ℝ} (hr : 0 < r)
    {s : ℕ} {f : ℝ × ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (ellipticAnnulus c (r / 2) (4 * r))))
    (hw : MemLp (fun p ↦ f p / (localRadius c p ^ s : ℂ)) 2
      (volume.restrict (ellipticAnnulus c (r / 2) (4 * r)))) :
    r⁻¹ ^ (2 * s) * squareEnergy (ellipticAnnulus c (r / 2) (4 * r)) f ≤
      4 ^ (2 * s) * ∫ p in ellipticAnnulus c (r / 2) (4 * r), weightedDensity c s f p := by
  rw [squareEnergy, ← integral_const_mul, ← integral_const_mul]
  have hwI : IntegrableOn (weightedDensity c s f) (ellipticAnnulus c (r / 2) (4 * r)) :=
    hw.integrable_norm_pow (by decide)
  apply integral_mono_ae ((hf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).const_mul _)
    (hwI.const_mul _)
  have hB := (isOpen_ellipticAnnulus c (r / 2) (4 * r)).measurableSet
  filter_upwards [ae_restrict_mem hB] with p hp
  change r / 2 < localRadius c p ∧ localRadius c p < 4 * r at hp
  have hp₀ : 0 < localRadius c p := (half_pos hr).trans hp.1
  have hh : r⁻¹ * localRadius c p ≤ 4 := by
    calc
      _ ≤ r⁻¹ * (4 * r) := mul_le_mul_of_nonneg_left hp.2.le (inv_nonneg.mpr hr.le)
      _ = 4 := by field_simp
  have hpow := pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr hr.le) hp₀.le) hh (2 * s)
  rw [mul_pow] at hpow
  have he := mul_le_mul_of_nonneg_right hpow (sq_nonneg ‖f p / (localRadius c p ^ s : ℂ)‖)
  unfold weightedDensity
  conv_lhs =>
    rw [radial_norm_factor c p s (f p) hp₀, mul_pow, ← pow_mul, Nat.mul_comm s 2, ← mul_assoc]
  exact he

private theorem weighted_inner_energy {c : ℝ × ℝ} {r : ℝ} (hr : 0 < r)
    {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (ellipticAnnulus c r (2 * r)))) :
    MemLp (fun p ↦ f p / (localRadius c p : ℂ)) 2
        (volume.restrict (ellipticAnnulus c r (2 * r))) ∧
      (∫ p in ellipticAnnulus c r (2 * r), ‖f p / (localRadius c p : ℂ)‖ ^ 2) ≤
        r⁻¹ ^ 2 * squareEnergy (ellipticAnnulus c r (2 * r)) f := by
  have hR : Continuous (fun p ↦ (localRadius c p : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_localRadius c)
  have hpw : ∀ᵐ p ∂volume.restrict (ellipticAnnulus c r (2 * r)),
      ‖f p / (localRadius c p : ℂ)‖ ≤ r⁻¹ * ‖f p‖ := by
    have hA := (isOpen_ellipticAnnulus c r (2 * r)).measurableSet
    filter_upwards [ae_restrict_mem hA] with p hp
    have hp₁ : r < localRadius c p := hp.1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr.trans hp₁),
      div_eq_mul_inv, mul_comm ‖f p‖]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hr hp₁.le) (norm_nonneg _)
  have hw := hf.of_le_mul (hf.aestronglyMeasurable.div₀ hR.aestronglyMeasurable) hpw
  refine ⟨hw, ?_⟩
  rw [squareEnergy, ← integral_const_mul]
  apply integral_mono_ae (hw.integrable_norm_pow (by decide))
    ((hf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).const_mul _)
  filter_upwards [hpw] with p h
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

private def jetDensity (k s : ℕ) (c : ℝ × ℝ)
    (J : List (Fin 2) → ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ∑ w : Fin k → Fin 2, weightedDensity c s (J (List.ofFn w)) p

private theorem jetDensity_nonneg (k s : ℕ) (c : ℝ × ℝ)
    (J : List (Fin 2) → ℝ × ℝ → ℂ) (p : ℝ × ℝ) : 0 ≤ jetDensity k s c J p :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

private theorem integrable_jetDensity {U : Set (ℝ × ℝ)} {k s : ℕ} {c : ℝ × ℝ}
    {J : List (Fin 2) → ℝ × ℝ → ℂ} (h : RadialJetLp k s U c J) :
    IntegrableOn (jetDensity k s c J) U :=
  integrable_finsetSum _ fun w _ ↦
    (h (List.ofFn w) List.length_ofFn).integrable_norm_pow (by decide)

private theorem outer_jet_energy {c : ℝ × ℝ} {r : ℝ} (hr : 0 < r) {k s : ℕ}
    {J : List (Fin 2) → ℝ × ℝ → ℂ}
    (h : RadialJetLp k s (ellipticAnnulus c (r / 2) (4 * r)) c J)
    (hL : ∀ w, w.length = k → MemLp (J w) 2
      (volume.restrict (ellipticAnnulus c (r / 2) (4 * r)))) :
    r⁻¹ ^ (2 * s) * radialJetEnergy k 0 (ellipticAnnulus c (r / 2) (4 * r)) c J ≤
      4 ^ (2 * s) * ∫ p in ellipticAnnulus c (r / 2) (4 * r), jetDensity k s c J p := by
  unfold radialJetEnergy jetDensity
  have hI (w : Fin k → Fin 2) :
      IntegrableOn (weightedDensity c s (J (List.ofFn w))) (ellipticAnnulus c (r / 2) (4 * r)) :=
    (h (List.ofFn w) List.length_ofFn).integrable_norm_pow (by decide)
  rw [integral_finsetSum _ (fun w _ ↦ hI w), Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w _
  simpa only [pow_zero, div_one, squareEnergy] using
    weighted_outer_energy hr (hL (List.ofFn w) List.length_ofFn) (h (List.ofFn w) List.length_ofFn)


/-- Dyadic summation of the interior Poisson estimate
(`lem:elliptic-weighted-third`). Shrinking avoids the outer boundary. -/
theorem elliptic_weighted_third {c : ℝ × ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    {u F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    {G : Fin 2 → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn 2 (localDisk c ρ) u D)
    (hw : ∀ k ≤ 2, RadialJetLp k (4 - k) (localDisk c ρ) c D)
    (hG : ∀ j, HasWeakPartialOn (localDisk c ρ) j F (G j))
    (hGw : ∀ j, MemLp (fun p ↦ G j p / (localRadius c p : ℂ)) 2
      (volume.restrict (localDisk c ρ)))
    (hΔ : ∀ᵐ p ∂(volume.restrict (localDisk c ρ)), D [0, 0] p + D [1, 1] p = F p) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ ρ ∧ ∃ E : List (Fin 2) → ℝ × ℝ → ℂ,
      HasWeakJetOn 3 (localDisk c σ) u E ∧
      (∀ w, w.length ≤ 2 → E w = D w) ∧ RadialJetLp 3 1 (localDisk c σ) c E := by
  let U := localDisk c ρ
  have hU : IsOpen U := isOpen_localDisk c ρ
  have hDL (w : List (Fin 2)) (hlen : w.length ≤ 2) : MemLp (D w) 2 (volume.restrict U) :=
    memLp_of_div_localRadius_pow (hw w.length hlen w rfl)
  have hu : MemSobolevOn 2 U u := memSobolevOn_iff_exists_weakJet.mpr ⟨D, hD, hDL⟩
  have hF2 : MemLp (fun p ↦ F p / (localRadius c p ^ 2 : ℂ)) 2 (volume.restrict U) := by
    have ht (j : Fin 2) := hw 2 le_rfl [j, j] (by simp)
    apply ((ht 0).add (ht 1)).ae_eq
    filter_upwards [hΔ] with p hp
    simpa only [Pi.add_apply, ← add_div] using
      congrArg (· / (localRadius c p ^ 2 : ℂ)) hp
  have hFL := memLp_of_div_localRadius_pow hF2
  have hGL (j : Fin 2) : MemLp (G j) 2 (volume.restrict U) :=
    memLp_of_div_localRadius_pow (s := 1) (by simpa only [pow_one] using hGw j)
  have hF : MemSobolevOn 1 U F :=
    ⟨hFL, fun j ↦ ⟨G j, hG j, hGL j⟩⟩
  let J : List (Fin 2) → ℝ × ℝ → ℂ
    | [] => F
    | j :: _ => G j
  have hJ : HasWeakJetOn 1 U F J := by
    refine ⟨rfl, fun w hl j ↦ ?_⟩
    rw [List.length_eq_zero_iff.mp (by omega : w.length = 0)]
    exact hG j
  have hJ0 : RadialJetLp 0 2 U c J := by
    intro w hl
    rw [List.length_eq_zero_iff.mp hl]
    exact hF2
  have hJ1 : RadialJetLp 1 1 U c J := by
    rintro (_ | ⟨j, w⟩) hl
    · simp at hl
    · simpa only [J, pow_one] using hGw j
  have hJw (w : List (Fin 2)) (_ : w.length ≤ 1) : MemLp (J w) 2 (volume.restrict U) := by
    cases w with
    | nil => exact hFL
    | cons j _ => exact hGL j
  have hu₃ := elliptic_local_h3 hU hu.memSobolevLocOn hF.memSobolevLocOn hD hΔ
  let V := localDisk c (ρ / 2)
  have hV : IsOpen V := isOpen_localDisk c _
  have hVcmp : IsCompact (closure V) := by
    apply (isCompact_closure_ellipticAnnulus c (-1) (ρ / 2)).of_isClosed_subset isClosed_closure
    apply closure_mono
    intro p hp
    exact ⟨(by norm_num : (-1 : ℝ) < 0).trans_le (Real.sqrt_nonneg _), hp⟩
  have hVU : closure V ⊆ U := by
    have hs : closure V ⊆ {p | localRadius c p ≤ ρ / 2} :=
      closure_minimal (fun p hp ↦ show localRadius c p ≤ ρ / 2 from le_of_lt hp)
        (isClosed_le (continuous_localRadius c) continuous_const)
    intro p hp
    change localRadius c p < ρ
    exact (show localRadius c p ≤ ρ / 2 from hs hp).trans_lt (by linarith)
  have hvu := subset_closure.trans hVU
  obtain ⟨E₀, hE₀, _⟩ := memSobolevOn_iff_exists_weakJet.mp (hu₃ V hV hVcmp hVU)
  let E (w : List (Fin 2)) := if w.length ≤ 2 then D w else E₀ w
  have he (w : List (Fin 2)) (hl : w.length ≤ 2) : E w = D w := ite_eq_left hl
  have he₃ (w : List (Fin 2)) (hl : w.length = 3) : E w = E₀ w := ite_eq_right (by omega)
  have hae (w : List (Fin 2)) (hl : w.length ≤ 3) : ∀ᵐ p, p ∈ V → E₀ w p = E w p := by
    by_cases hw : w.length ≤ 2
    · rw [he w hw]
      have hE₂ : HasWeakJetOn 2 V u E₀ := ⟨hE₀.1, fun v h ↦ hE₀.2 v (by omega)⟩
      exact hE₂.ae_eq hV (hD.mono hvu) w hw
    · rw [he₃ w (by omega)]
      exact Eventually.of_forall fun _ _ ↦ rfl
  have hE : HasWeakJetOn 3 V u E := by
    refine ⟨(he [] (by decide)).trans hD.1, fun w hl j ↦ ?_⟩
    exact (hE₀.2 w hl j).congr_ae_on hV.measurableSet (hae w hl.le)
      (hae (j :: w) (by simp; omega))
  let σ := ρ / 16
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσV : localDisk c σ ⊆ V := fun p hp ↦
    (show localRadius c p < ρ / 16 from hp).trans (by linarith)
  refine ⟨σ, hσ, by dsimp [σ]; linarith, E, hE.mono hσV, he, ?_⟩
  intro w hw₃
  let a := shellRadius σ
  let A (n : ℕ) := ellipticAnnulus c (a n) (2 * a n)
  let B (n : ℕ) := ellipticAnnulus c (a n / 2) (4 * a n)
  have hBV (n : ℕ) : B n ⊆ V := by
    intro p hp
    have ha : a n ≤ σ := (shellRadius_antitone hσ (Nat.zero_le n)).trans_eq (by simp [shellRadius])
    change localRadius c p < ρ / 2
    have hpr : localRadius c p < 4 * a n := hp.2
    change a n ≤ ρ / 16 at ha
    linarith
  have hBU (n : ℕ) := (hBV n).trans hvu
  let H (p : ℝ × ℝ) := jetDensity 1 1 c J p + jetDensity 0 2 c J p + jetDensity 0 4 c D p
  have hH₁ := integrable_jetDensity hJ1
  have hH₂ := integrable_jetDensity hJ0
  have hH₄ := integrable_jetDensity (hw 0 (by decide))
  have hH : IntegrableOn H U := (hH₁.add hH₂).add hH₄
  have hHpos (p : ℝ × ℝ) : 0 ≤ H p :=
    add_nonneg (add_nonneg (jetDensity_nonneg ..) (jetDensity_nonneg ..)) (jetDensity_nonneg ..)
  obtain ⟨C, hC, hest⟩ := elliptic_dyadic
  have hlocal (n : ℕ) :
      MemLp (fun p ↦ E w p / (localRadius c p : ℂ)) 2 (volume.restrict (A n)) ∧
      (∫ p in A n, ‖E w p / (localRadius c p : ℂ)‖ ^ 2) ≤ C * 4 ^ 8 * ∫ p in B n, H p := by
    have hr : 0 < a n := shellRadius_pos hσ n
    have hm := Measure.restrict_mono (hBU n) (le_refl (volume : Measure (ℝ × ℝ)))
    have hΔB : ∀ᵐ p ∂volume.restrict (B n), E [0, 0] p + E [1, 1] p = F p := by
      rw [he [0, 0] (by decide), he [1, 1] (by decide)]
      exact ae_mono hm hΔ
    have h := hest c (a n) hr u F E J (hu.mono (hBU n)) (hF.mono (hBU n))
      (hE.mono (hBV n)) (hJ.mono (hBU n)) hΔB
    have hL : MemLp (E w) 2 (volume.restrict (A n)) := by
      have hh := h.1 w hw₃
      simp only [pow_zero, div_one] at hh
      exact hh
    have hinner := weighted_inner_energy hr hL
    refine ⟨hinner.1, hinner.2.trans ?_⟩
    have hsum : squareEnergy (A n) (E w) ≤ radialJetEnergy 3 0 (A n) c E := by
      let v : Fin 3 → Fin 2 := fun i ↦ w.get (Fin.cast hw₃.symm i)
      have hv : List.ofFn v = w := (List.ofFn_congr hw₃ w.get).symm.trans (List.ofFn_get w)
      rw [radialJetEnergy]
      simp only [pow_zero, div_one]
      change squareEnergy (A n) (E w) ≤ ∑ x : Fin 3 → Fin 2, squareEnergy (A n) (E (List.ofFn x))
      rw [← hv]
      exact Finset.single_le_sum (f := fun x ↦ squareEnergy (A n) (E (List.ofFn x)))
        (fun _ _ ↦ squareEnergy_nonneg _ _) (Finset.mem_univ v)
    have h1 := outer_jet_energy hr (hJ1.mono (hBU n))
      (fun w hw ↦ (hJw w hw.le).mono_measure hm)
    have h2 := outer_jet_energy hr (hJ0.mono (hBU n))
      (fun w hw ↦ (hJw w (by omega)).mono_measure hm)
    have h4 := outer_jet_energy hr ((hw 0 (by decide)).mono (hBU n))
      (fun w hw ↦ (hDL w (by omega)).mono_measure hm)
    have hBm : MeasurableSet (B n) := (isOpen_ellipticAnnulus c _ _).measurableSet
    have h1' : 0 ≤ ∫ p in B n, jetDensity 1 1 c J p :=
      setIntegral_nonneg hBm (fun p _ ↦ jetDensity_nonneg 1 1 c J p)
    have h2' : 0 ≤ ∫ p in B n, jetDensity 0 2 c J p :=
      setIntegral_nonneg hBm (fun p _ ↦ jetDensity_nonneg 0 2 c J p)
    have hHi : (∫ p in B n, H p) = (∫ p in B n, jetDensity 1 1 c J p) +
        (∫ p in B n, jetDensity 0 2 c J p) + ∫ p in B n, jetDensity 0 4 c D p := by
      have ha := hH₁.mono_set (hBU n)
      have hb := hH₂.mono_set (hBU n)
      have hc := hH₄.mono_set (hBU n)
      exact (integral_add (ha.add hb) hc).trans (congrArg (· + _) (integral_add ha hb))
    have houter :
        (a n)⁻¹ ^ 2 * radialJetEnergy 1 0 (B n) c J +
          (a n)⁻¹ ^ 4 * radialJetEnergy 0 0 (B n) c J +
          (a n)⁻¹ ^ 8 * radialJetEnergy 0 0 (B n) c D ≤ 4 ^ 8 * ∫ p in B n, H p := by
      rw [hHi]
      change (a n)⁻¹ ^ 2 * radialJetEnergy 1 0 (B n) c J ≤ _ at h1
      change (a n)⁻¹ ^ 4 * radialJetEnergy 0 0 (B n) c J ≤ _ at h2
      change (a n)⁻¹ ^ 8 * radialJetEnergy 0 0 (B n) c D ≤ _ at h4
      linarith only [h1, h2, h4, h1', h2']
    calc
      _ ≤ (a n)⁻¹ ^ 2 * radialJetEnergy 3 0 (A n) c E :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ ≤ (a n)⁻¹ ^ 2 * (C * (radialJetEnergy 1 0 (B n) c J +
          (a n)⁻¹ ^ 2 * radialJetEnergy 0 0 (B n) c J +
          (a n)⁻¹ ^ 6 * radialJetEnergy 0 0 (B n) c D)) := by
        have hE0 : radialJetEnergy 0 0 (B n) c E = radialJetEnergy 0 0 (B n) c D := by
          unfold radialJetEnergy
          apply Finset.sum_congr rfl
          intro v _
          rw [he (List.ofFn v) (by simp)]
        have h' : radialJetEnergy 3 0 (A n) c E ≤ C * (radialJetEnergy 1 0 (B n) c J +
            (a n)⁻¹ ^ 2 * radialJetEnergy 0 0 (B n) c J +
            (a n)⁻¹ ^ 6 * radialJetEnergy 0 0 (B n) c E) := h.2
        rw [hE0] at h'
        exact mul_le_mul_of_nonneg_left h' (sq_nonneg _)
      _ = C * ((a n)⁻¹ ^ 2 * radialJetEnergy 1 0 (B n) c J +
          (a n)⁻¹ ^ 4 * radialJetEnergy 0 0 (B n) c J +
          (a n)⁻¹ ^ 8 * radialJetEnergy 0 0 (B n) c D) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left houter hC.le).trans_eq (by ring)
  have hf := memLp_of_shell_bounds
    (fun n ↦ (isOpen_ellipticAnnulus c (a n / 2) (4 * a n)).measurableSet) hBU
    (shell_overlap hσ c) (by positivity : 0 ≤ C * 4 ^ 8) hH hHpos
    (fun n ↦ (hlocal n).1) (fun n ↦ (hlocal n).2)
  have hh := hf.mono_measure (Measure.restrict_mono (shell_cover hσ c) le_rfl)
  have hnull : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ≠ c := by
    rw [ae_iff]
    simp [Measure.volume_eq_prod]
  have hrestr : volume.restrict (localDisk c σ \ {c}) = volume.restrict (localDisk c σ) := by
    apply Measure.restrict_congr_set
    filter_upwards [hnull] with p hp
    simp [hp]
  rw [hrestr] at hh
  simpa only [pow_one] using hh

end NoEmbeddedEigenvalues
