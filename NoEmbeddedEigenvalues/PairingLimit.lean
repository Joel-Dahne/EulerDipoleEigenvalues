import NoEmbeddedEigenvalues.Melnikov

/-!
# Limit of the transport pairing at the separatrix

Blueprint: `lem:forcing-comparison`, `lem:quarter-pairing-limit`,
`lem:pairing-limit`, `lem:ee-transport-traces`.

Separate the quantitative forcing comparison from the quarter-orbit transport
limit, then assemble the four quarters along the common good sequence. The finite
pairing error is controlled by `L² h^(1/4)` and `L exp(-L/2)`. Thus only the global
upper bound for `exp L` and `L → ∞` are used, not sharp or two-sided period
asymptotics. The canonical pairing has integrable exponential tails.

Both orbit and arc pairings are invariant under the quarter character, so the full
limit is four times the base-quarter limit. Nonresonant periodic uniqueness already
supplies the vorticity character on the selected orbits; no planar a.e. rotation
hypothesis on `v` is needed. The final eigenfunction specialization changes back to
the raw stream representative outside one additional null set of levels.

The pairing-limit results and their trace, chart/coarea, Hölder, periodization,
orbit-comparison and period-bound prerequisites are proved without admissions.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open Real Complex MeasureTheory Set Filter
open scoped Topology Interval ComplexConjugate

/-- Exponential distance to the positive-time saddle endpoint. -/
theorem dist_arc_pos_le (s : ℝ) :
    dist (separatrixArc s) (0, -π) ≤ 2 * Real.exp (-s) := by
  have ha := arcAngle_mem_Ioo s
  have he : dist (separatrixArc s) (0, -π) = arcAngle s := by
    simp [separatrixArc, Prod.dist_eq, abs_of_pos ha.1]
  rw [he, arcAngle]
  exact mul_le_mul_of_nonneg_left (arctan_le_self (Real.exp_pos _).le) (by norm_num)

/-- Exponential distance to the negative-time saddle endpoint. -/
theorem dist_arc_neg_le (s : ℝ) :
    dist (separatrixArc s) (π, 0) ≤ 2 * Real.exp s := by
  have ha := arcAngle_mem_Ioo s
  have he : dist (separatrixArc s) (π, 0) = π - arcAngle s := by
    simp [separatrixArc, Prod.dist_eq, Real.dist_eq, abs_of_neg (sub_neg.2 ha.2)]
  have harc : π - arcAngle s = 2 * arctan (Real.exp s) := by
    rw [arcAngle, Real.exp_neg, arctan_inv_of_pos (Real.exp_pos _)]
    ring
  rw [he, harc]
  exact mul_le_mul_of_nonneg_left (arctan_le_self (Real.exp_pos _).le) (by norm_num)

/-- Uniform boundedness and fixed-exponent Hölder comparison of orbit and arc forcings,
    including exponential approach of the arc forcing to its complex saddle values. -/
theorem exists_forcing_comparison {U : Set (ℝ × ℝ)} (hUo : IsOpen U)
    (hU : closure cellSquare ⊆ U) {f : ℝ × ℝ → ℂ}
    (hfc : ContinuousOn f U) (hf : MemSobolevOn 2 U f) :
    ∃ C M h₀ : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧
      (∀ s, ‖f (separatrixArc s)‖ ≤ M) ∧
      (∀ s, 0 ≤ s → ‖f (separatrixArc s) - f (0, -π)‖ ≤ C * Real.exp (-(1 / 2) * s)) ∧
      (∀ s, s ≤ 0 → ‖f (separatrixArc s) - f (π, 0)‖ ≤ C * Real.exp ((1 / 2) * s)) ∧
      ∀ h ∈ Ioo 0 h₀, ∀ s, |s| ≤ eighthPeriod h →
        ‖f (dipoleOrbit h s) - f (separatrixArc s)‖ ≤ C * h ^ (1 / 4 : ℝ) ∧
        ‖f (dipoleOrbit h s)‖ ≤ M := by
  have hK := arcSegment_subset_closure_cellSquare.trans hU
  obtain ⟨ρ, hρ, CH, hCH, hH⟩ := exists_holder_near_arcSegment hUo hK hfc hf
    (α := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨Co, ho, hho, hclose⟩ := orbit_close_arc
  obtain ⟨M₀, hM₀⟩ := isCompact_arcSegment.exists_bound_of_continuousOn (hfc.mono hK)
  let Co' := max Co 0
  have hCo' : 0 ≤ Co' := le_max_right _ _
  let A := CH * Co' ^ (1 / 2 : ℝ)
  let B := CH * (2 : ℝ) ^ (1 / 2 : ℝ)
  let C := A + B
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  have hC : 0 ≤ C := add_nonneg hA hB
  have hc : Continuous (fun h : ℝ ↦ Co' * √h) := by fun_prop
  obtain ⟨η, hη, hsmall⟩ := Metric.continuousAt_iff.1 (hc.continuousAt (x := 0)) ρ hρ
  simp only [Real.sqrt_zero, mul_zero, Real.dist_eq, sub_zero] at hsmall
  let h₀ := min η (min ho 1)
  have hh₀ : 0 < h₀ := lt_min hη (lt_min hho zero_lt_one)
  have hself (p : ℝ × ℝ) (hp : p ∈ arcSegment) : p ∈ Metric.thickening ρ arcSegment :=
    Metric.self_subset_thickening hρ _ hp
  have hend (s : ℝ) (p : ℝ × ℝ) (hp : p ∈ arcSegment) (r : ℝ)
      (hdist : dist (separatrixArc s) p ≤ 2 * Real.exp r) :
      ‖f (separatrixArc s) - f p‖ ≤ C * Real.exp (r / 2) := by
    calc
      _ ≤ CH * dist (separatrixArc s) p ^ (1 / 2 : ℝ) :=
        hH _ (hself _ (separatrixArc_mem_arcSegment s)) _ (hself _ hp)
      _ ≤ CH * (2 * Real.exp r) ^ (1 / 2 : ℝ) := by gcongr
      _ = B * Real.exp (r / 2) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos _).le, ← Real.exp_mul]
        dsimp only [B]
        rw [show r * (1 / 2 : ℝ) = r / 2 by ring]
        ring
      _ ≤ C * Real.exp (r / 2) := by dsimp only [C]; gcongr; linarith
  refine ⟨C, max M₀ 0 + C, h₀, hC, by positivity, hh₀,
    (min_le_right _ _).trans (min_le_right _ _), ?_, ?_, ?_, ?_⟩
  · intro s
    exact (hM₀ _ (separatrixArc_mem_arcSegment s)).trans
      ((le_max_left M₀ 0).trans (le_add_of_nonneg_right hC))
  · intro s _
    simpa only [show -s / 2 = -(1 / 2 : ℝ) * s by ring] using
      hend s _ saddle_pos_mem_arcSegment (-s) (dist_arc_pos_le s)
  · intro s _
    simpa only [show s / 2 = (1 / 2 : ℝ) * s by ring] using
      hend s _ saddle_neg_mem_arcSegment s (dist_arc_neg_le s)
  · intro h hh s hs
    have hh1 : h < 1 := hh.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hnear : Co' * √h < ρ := (le_abs_self _).trans_lt
      (hsmall (by simpa [abs_of_pos hh.1] using hh.2.trans_le (min_le_left _ _)))
    have hd : dist (dipoleOrbit h s) (separatrixArc s) ≤ Co' * √h := by
      rw [dist_eq_norm]
      exact (hclose h ⟨hh.1, hh.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
        s hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
    have horbit : dipoleOrbit h s ∈ Metric.thickening ρ arcSegment :=
      Metric.mem_thickening_iff.2 ⟨_, separatrixArc_mem_arcSegment s, hd.trans_lt hnear⟩
    have hdiff : ‖f (dipoleOrbit h s) - f (separatrixArc s)‖ ≤ C * h ^ (1 / 4 : ℝ) := by
      calc
        _ ≤ CH * dist (dipoleOrbit h s) (separatrixArc s) ^ (1 / 2 : ℝ) :=
          hH _ horbit _ (hself _ (separatrixArc_mem_arcSegment s))
        _ ≤ CH * (Co' * √h) ^ (1 / 2 : ℝ) := by gcongr
        _ = A * h ^ (1 / 4 : ℝ) := by
          rw [Real.mul_rpow hCo' (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
            ← Real.rpow_mul hh.1.le, show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num]
          simp only [A, mul_assoc]
        _ ≤ C * h ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith)
            (Real.rpow_nonneg hh.1.le _)
    refine ⟨hdiff, ?_⟩
    have hpw : h ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hh.1.le hh1.le (by norm_num)
    calc
      ‖f (dipoleOrbit h s)‖ ≤ ‖f (dipoleOrbit h s) - f (separatrixArc s)‖ +
          ‖f (separatrixArc s)‖ := norm_le_norm_sub_add _ _
      _ ≤ C * h ^ (1 / 4 : ℝ) + M₀ := add_le_add hdiff (hM₀ _ (separatrixArc_mem_arcSegment s))
      _ ≤ max M₀ 0 + C := by nlinarith [mul_le_mul_of_nonneg_left hpw hC, le_max_left M₀ 0]

private theorem eighthPeriod_rate_limits {hs : ℕ → ℝ}
    (hh : ∀ n, hs n ∈ Ioo 0 1) (hlim : Tendsto hs atTop (𝓝 0)) :
    Tendsto (fun n ↦ eighthPeriod (hs n)) atTop atTop ∧
      Tendsto (fun n ↦ eighthPeriod (hs n) * hs n ^ (1 / 4 : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eighthPeriod (hs n) ^ 2 * hs n ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
  have hlim' : Tendsto hs atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n ↦ (hh n).1⟩
  have htop : Tendsto (fun n ↦ eighthPeriod (hs n)) atTop atTop := by
    have h := (tendsto_orbitPeriod_atTop.comp hlim').atTop_div_const (by norm_num : (0 : ℝ) < 8)
    simpa only [Function.comp_def, orbitPeriod, mul_div_cancel_left₀ _ (by norm_num : (8 : ℝ) ≠ 0)]
      using h
  obtain ⟨Ce, hCe⟩ := exp_eighthPeriod_le
  have hCe0 : 0 < Ce := by
    have hp := (Real.exp_pos _).trans_le (hCe (hs 0) (hh 0))
    exact (div_pos_iff.1 hp).elim (fun h ↦ h.1)
      (fun h ↦ absurd h.2 (not_lt.2 (Real.sqrt_nonneg _)))
  have hLle (n : ℕ) : eighthPeriod (hs n) ≤ Real.log Ce - (1 / 2) * Real.log (hs n) := by
    have hp := (Real.exp_pos _).trans_le (hCe (hs n) (hh n))
    have hb := (Real.le_log_iff_exp_le hp).2 (hCe (hs n) (hh n))
    rw [Real.log_div hCe0.ne' (Real.sqrt_pos.2 (hh n).1).ne',
      Real.log_sqrt (hh n).1.le] at hb
    linarith
  have hp : Tendsto (fun n ↦ hs n ^ (1 / 8 : ℝ)) atTop (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 (1 / 8) (Or.inr (by norm_num))).tendsto.comp hlim
    simpa [Function.comp_def] using! h
  have hlog := (tendsto_log_mul_rpow_nhdsGT_zero (r := 1 / 8) (by norm_num)).comp hlim'
  have hupper : Tendsto (fun n ↦ (Real.log Ce - (1 / 2) * Real.log (hs n)) *
      hs n ^ (1 / 8 : ℝ)) atTop (𝓝 0) := by
    have h := (hp.const_mul (Real.log Ce)).sub (hlog.const_mul (1 / 2))
    simp only [mul_zero, sub_zero] at h
    exact h.congr fun n ↦ by dsimp only [Function.comp_def]; ring
  have hsmall : Tendsto (fun n ↦ eighthPeriod (hs n) * hs n ^ (1 / 8 : ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ mul_nonneg (eighthPeriod_pos (hh n).1 (hh n).2).le
      (Real.rpow_nonneg (hh n).1.le _))
      (fun n ↦ mul_le_mul_of_nonneg_right (hLle n) (Real.rpow_nonneg (hh n).1.le _)) hupper
  have hpow (n : ℕ) : hs n ^ (1 / 4 : ℝ) = hs n ^ (1 / 8 : ℝ) * hs n ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_add (hh n).1]
    norm_num
  refine ⟨htop, ?_, ?_⟩
  · have h := hsmall.mul hp
    simp only [mul_zero] at h
    exact h.congr fun n ↦ by rw [hpow]; ring
  · have h := hsmall.pow 2
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
    exact h.congr fun n ↦ by rw [hpow]; ring

/-- The two-sided exponential majorant for Hölder arc remainders is integrable. -/
theorem integrable_exp_neg_half_abs :
    Integrable (fun s : ℝ ↦ Real.exp (-(1 / 2) * |s|)) := by
  have hn : IntegrableOn (fun s : ℝ ↦ Real.exp (-(1 / 2) * |s|)) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1 / 2) 0).congr_fun
      ?_ measurableSet_Iic
    intro s hs
    dsimp only
    rw [abs_of_nonpos (show s ≤ 0 from hs)]
    congr 1
    ring
  have hp : IntegrableOn (fun s : ℝ ↦ Real.exp (-(1 / 2) * |s|)) (Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 0).congr_fun
      ?_ measurableSet_Ioi
    intro s hs
    dsimp only
    rw [abs_of_pos (show 0 < s from hs)]
  simpa using hn.union hp

set_option maxHeartbeats 1600000 in
-- The endpoint estimate and ODE comparison are assembled with several integral limits.
/-- The pairing on a single quarter converges to the canonical arc pairing along
    any good sequence carrying ACL transport solutions with the quarter character. -/
theorem quarter_pairing_limit {lam : ℝ} {κ : ℂ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hU : closure cellSquare ⊆ U)
    (hκ : κ = 1 ∨ κ = -1 ∨ κ = I ∨ κ = -I) (hUR : ∀ p ∈ U, (p.2, -p.1) ∈ U)
    (hfR : ∀ p ∈ U, f (p.2, -p.1) = κ * f p) (hfc : ContinuousOn f U)
    {hs : ℕ → ℝ} (hh : ∀ n, hs n ∈ Ioo 0 1 ∧
      ∃ m : ℤ, |lam * orbitPeriod (hs n) - 2 * Real.pi * (m + 1 / 2)| < Real.pi / 3)
    (hlim : Tendsto hs atTop (𝓝 0)) {Z : ℕ → ℝ → ℂ}
    (hac : ∀ n a b, AbsolutelyContinuousOnInterval (Z n) a b)
    (hd : ∀ n, ∀ᵐ t, HasDerivAt (Z n)
      (I * (lam * Z n t + f (dipoleOrbit (hs n) t))) t)
    (hchar : ∀ n, Z n (eighthPeriod (hs n)) = κ * Z n (-eighthPeriod (hs n))) :
    Tendsto (fun n ↦ ∫ t in (-eighthPeriod (hs n))..eighthPeriod (hs n),
      ((-(lam : ℂ) * Z n t - f (dipoleOrbit (hs n) t)) *
        conj (f (dipoleOrbit (hs n) t))).re) atTop
      (𝓝 (∫ s, (canonicalProfile lam (f ∘ separatrixArc) s *
        conj (f (separatrixArc s))).re)) := by
  let g := f ∘ separatrixArc
  let Ω := canonicalProfile lam g
  let z := canonicalUnknown lam g
  let L : ℕ → ℝ := fun n ↦ eighthPeriod (hs n)
  have hLpos (n : ℕ) : 0 < L n := eighthPeriod_pos (hh n).1.1 (hh n).1.2
  obtain ⟨hLtop, hLr, hL2r⟩ := eighthPeriod_rate_limits (fun n ↦ (hh n).1) hlim
  obtain ⟨C, M, h₀, hC, hM, hh₀, -, hgB, hgp, hgm, hcomp⟩ :=
    exists_forcing_comparison hp.isOrbitUnion.1 hU hfc hp.memSobolevOn
  have hK := arcSegment_subset_closure_cellSquare.trans hU
  obtain ⟨hgac, hgdiff, hgi⟩ := arcTrace_regularity hp.isOrbitUnion.1 hK hfc hp.memSobolevOn
  have hMel := (melnikov_character hp hU hκ hUR hfR hfc).2
  obtain ⟨B, hΩ⟩ := norm_canonicalProfile_le_exp hgac hgi hMel (by norm_num : (0 : ℝ) < 1 / 2)
    hgp hgm
  have hB : 0 ≤ B := (norm_nonneg _).trans (by simpa using hΩ 0)
  have hΩB (t : ℝ) : ‖Ω t‖ ≤ B := (hΩ t).trans (by
    exact mul_le_of_le_one_right hB (Real.exp_le_one_iff.2
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (abs_nonneg _))))
  have hgc : Continuous g := continuous_of_absolutelyContinuous hgac
  have hΩc : Continuous Ω := continuous_of_absolutelyContinuous
    (absolutelyContinuousOnInterval_canonicalProfile hgi)
  have hzac (a b : ℝ) : AbsolutelyContinuousOnInterval z a b := by
    convert ((absolutelyContinuousOnInterval_canonicalProfile (lam := lam) hgi a b).add
      (hgac a b)).const_smul (-1 / (lam : ℂ)) using 1
    funext t
    dsimp [z, canonicalUnknown, g, Function.comp_def]
    ring
  have hzd := ae_hasDerivAt_canonicalUnknown_sub hp.ne_zero hgi hgdiff
  have hκnorm : ‖(κ : ℂ)‖ = 1 := by rcases hκ with rfl | rfl | rfl | rfl <;> simp [← pow_two, Complex.I_sq]
  have hends : f (0, -π) = κ * f (π, 0) := by
    simpa using hfR (π, 0) (hK saddle_neg_mem_arcSegment)
  let D : ℝ := 2 * (B + C) / |lam|
  have hD : 0 ≤ D := by positivity
  let ε : ℕ → ℝ := fun n ↦ C * hs n ^ (1 / 4 : ℝ)
  let β : ℕ → ℝ := fun n ↦ D * Real.exp (-(1 / 2) * L n)
  have hε (n : ℕ) : 0 ≤ ε n := mul_nonneg hC (Real.rpow_nonneg (hh n).1.1.le _)
  have hβ (n : ℕ) : 0 ≤ β n := mul_nonneg hD (Real.exp_pos _).le
  have hzboundary (n : ℕ) : ‖z (L n) - κ * z (-L n)‖ ≤ β n := by
    have heq : z (L n) - κ * z (-L n) =
        -((Ω (L n) - κ * Ω (-L n)) +
          ((g (L n) - f (0, -π)) - κ * (g (-L n) - f (π, 0)))) / lam := by
      dsimp [z, Ω, canonicalUnknown]
      rw [hends]
      ring
    rw [heq, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    have hpΩ : ‖Ω (L n)‖ ≤ B * Real.exp (-(1 / 2) * L n) := by
      simpa only [abs_of_pos (hLpos n)] using hΩ (L n)
    have hnΩ : ‖Ω (-L n)‖ ≤ B * Real.exp (-(1 / 2) * L n) := by
      simpa only [abs_neg, abs_of_pos (hLpos n)] using hΩ (-L n)
    have hpg := hgp (L n) (hLpos n).le
    have hng := hgm (-L n) (by linarith [hLpos n])
    have hnum : ‖(Ω (L n) - κ * Ω (-L n)) +
        ((g (L n) - f (0, -π)) - κ * (g (-L n) - f (π, 0)))‖ ≤
        2 * (B + C) * Real.exp (-(1 / 2) * L n) := by
      calc
        _ ≤ (‖Ω (L n)‖ + ‖κ * Ω (-L n)‖) +
            (‖g (L n) - f (0, -π)‖ + ‖κ * (g (-L n) - f (π, 0))‖) :=
          (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_sub_le _ _))
        _ ≤ 2 * (B + C) * Real.exp (-(1 / 2) * L n) := by
          rw [norm_mul, norm_mul, hκnorm, one_mul, one_mul]
          dsimp only [g, Function.comp_def]
          rw [show (1 / 2 : ℝ) * -L n = -(1 / 2) * L n by ring] at hng
          nlinarith
    calc
      _ ≤ (2 * (B + C) * Real.exp (-(1 / 2) * L n)) / |lam| :=
        div_le_div_of_nonneg_right hnum (abs_nonneg _)
      _ = β n := by dsimp [β, D]; ring
  let δ : ℝ := 1 / 4
  have hδ : 0 < δ := by norm_num [δ]
  let A : ℕ → ℝ := fun n ↦ |lam| * ((β n + 2 * L n * ε n) / δ + 2 * L n * ε n) + ε n
  let E : ℕ → ℝ := fun n ↦ (A n * M + B * ε n) * (2 * L n)
  let P : ℕ → ℝ := fun n ↦ ∫ t in (-L n)..L n,
    ((-(lam : ℂ) * Z n t - f (dipoleOrbit (hs n) t)) * conj (f (dipoleOrbit (hs n) t))).re
  let T : ℕ → ℝ := fun n ↦ ∫ t in (-L n)..L n, (Ω t * conj (g t)).re
  have herror (n : ℕ) (hn : hs n < h₀) : |P n - T n| ≤ E n := by
    let G : ℝ → ℂ := fun t ↦ f (dipoleOrbit (hs n) t)
    have hGc : Continuous G := hfc.comp_continuous
      (continuous_dipoleOrbit.comp (continuous_const.prodMk continuous_id))
      (fun t ↦ hU (subset_closure (dipoleOrbit_mem_cellSquare (hh n).1.1 (hh n).1.2 t)))
    have hZc := continuous_of_absolutelyContinuous (hac n)
    have hpt (t : ℝ) (ht : t ∈ Icc (-L n) (L n)) :
        ‖G t - g t‖ ≤ ε n ∧ ‖G t‖ ≤ M :=
      hcomp _ ⟨(hh n).1.1, hn⟩ _ (abs_le.2 ht)
    have hWac := (hac n (-L n) (L n)).sub (hzac (-L n) (L n))
    have hWd : ∀ᵐ t, t ∈ uIcc (-L n) (L n) →
        HasDerivAt (fun t ↦ Z n t - z t)
          (I * (lam * (Z n t - z t) + (G t - g t))) t := by
      filter_upwards [hd n, hzd] with t ht hz _
      convert ht.sub hz using 1
      ring
    have hdiv : δ ≤ ‖exp (I * lam * ((L n : ℂ) - (-L n : ℝ))) - κ‖ := by
      obtain ⟨m, hm⟩ := (hh n).2
      have hk : κ ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul]
        rcases hκ with rfl | rfl | rfl | rfl <;> norm_num [neg_sq, Complex.I_sq]
      have hb := norm_exp_sub_ge_of_goodWindow_fourthRoot hm hk
      convert hb using 1
      congr 2
      dsimp only [L, orbitPeriod]
      push_cast
      congr 1
      ring
    have hwb : ‖(Z n (L n) - z (L n)) - κ * (Z n (-L n) - z (-L n))‖ ≤ β n := by
      rw [hchar n, show (κ : ℂ) * Z n (-L n) - z (L n) -
        κ * (Z n (-L n) - z (-L n)) = -(z (L n) - κ * z (-L n)) by ring, norm_neg]
      exact hzboundary n
    have hW (t : ℝ) (ht : t ∈ Icc (-L n) (L n)) :
        ‖Z n t - z t‖ ≤ (β n + 2 * L n * ε n) / δ + 2 * L n * ε n := by
      have hb := norm_transport_le_of_boundary (by linarith [hLpos n]) (hε n) hδ
        hWac ((hGc.sub hgc).intervalIntegrable _ _) hWd
        (fun t ht ↦ (hpt t ht).1) hdiv ht
      calc
        _ ≤ (‖(Z n (L n) - z (L n)) - κ * (Z n (-L n) - z (-L n))‖ +
            ε n * (L n - -L n)) / δ + ε n * (L n - -L n) := hb
        _ ≤ (β n + 2 * L n * ε n) / δ + 2 * L n * ε n := by
          have hlen : ε n * (L n - -L n) = 2 * L n * ε n := by ring
          rw [hlen]
          gcongr
    have hV (t : ℝ) (ht : t ∈ Icc (-L n) (L n)) :
        ‖(-(lam : ℂ) * Z n t - G t) - Ω t‖ ≤ A n := by
      have heq : (-(lam : ℂ) * Z n t - G t) - Ω t =
          -(lam : ℂ) * (Z n t - z t) - (G t - g t) := by
        dsimp [z, Ω, canonicalUnknown]
        field_simp [ofReal_ne_zero.2 hp.ne_zero]
        ring
      rw [heq]
      calc
        _ ≤ ‖-(lam : ℂ) * (Z n t - z t)‖ + ‖G t - g t‖ := norm_sub_le _ _
        _ = |lam| * ‖Z n t - z t‖ + ‖G t - g t‖ := by
          rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ A n := add_le_add (mul_le_mul_of_nonneg_left (hW t ht) (abs_nonneg _)) (hpt t ht).1
    have hA : 0 ≤ A n := by
      have hεn := hε n
      have hβn := hβ n
      have hLn := (hLpos n).le
      dsimp only [A]
      positivity
    have hpint : IntervalIntegrable (fun t ↦ ((-(lam : ℂ) * Z n t - G t) * conj (G t)).re)
        volume (-L n) (L n) := (by fun_prop : Continuous
          (fun t ↦ ((-(lam : ℂ) * Z n t - G t) * conj (G t)).re)).intervalIntegrable _ _
    have htint : IntervalIntegrable (fun t ↦ (Ω t * conj (g t)).re) volume (-L n) (L n) :=
      (by fun_prop : Continuous (fun t ↦ (Ω t * conj (g t)).re)).intervalIntegrable _ _
    have hb := abs_integral_pairing_sub_le (by linarith [hLpos n]) hA hB hpint htint hV
      (fun t _ ↦ hΩB t) (fun t ht ↦ (hpt t ht).2) (fun t ht ↦ (hpt t ht).1)
    simpa only [P, T, E, show L n - -L n = 2 * L n by ring] using hb
  have hLe : Tendsto (fun n ↦ L n * ε n) atTop (𝓝 0) := by
    simpa only [ε, mul_zero, mul_left_comm, mul_assoc] using hLr.const_mul C
  have hL2e : Tendsto (fun n ↦ L n ^ 2 * ε n) atTop (𝓝 0) := by
    simpa only [ε, mul_zero, mul_left_comm, mul_assoc] using hL2r.const_mul C
  have hLb : Tendsto (fun n ↦ L n * β n) atTop (𝓝 0) := by
    have hb := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (1 / 2)
      (by norm_num)).comp hLtop
    simpa [Function.comp_def, Real.rpow_one, β, mul_left_comm, mul_assoc] using hb.const_mul D
  have hE : Tendsto E atTop (𝓝 0) := by
    have he := ((hLb.const_mul (2 * M * |lam| / δ)).add
      (hL2e.const_mul (4 * M * |lam| * (1 / δ + 1)))).add
      (hLe.const_mul (2 * (M + B)))
    simp only [mul_zero, add_zero] at he
    exact he.congr fun n ↦ by dsimp only [E, A]; ring
  have hdiff : Tendsto (fun n ↦ P n - T n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ hE
    filter_upwards [hlim.eventually (gt_mem_nhds hh₀)] with n hn
    exact herror n hn
  have hInt : Integrable (fun t ↦ (Ω t * conj (g t)).re) := by
    refine (integrable_exp_neg_half_abs.const_mul (B * M)).mono'
      (by fun_prop : Continuous (fun t ↦ (Ω t * conj (g t)).re)).aestronglyMeasurable ?_
    refine Eventually.of_forall fun t ↦ ?_
    calc
      ‖(Ω t * conj (g t)).re‖ ≤ ‖Ω t * conj (g t)‖ := by
        simpa only [Real.norm_eq_abs] using abs_re_le_norm (Ω t * conj (g t))
      _ = ‖Ω t‖ * ‖g t‖ := by rw [norm_mul, norm_conj]
      _ ≤ (B * Real.exp (-(1 / 2) * |t|)) * M :=
        mul_le_mul (hΩ t) (hgB t) (norm_nonneg _) (by positivity)
      _ = (B * M) * Real.exp (-(1 / 2) * |t|) := by ring
  have hT := intervalIntegral_tendsto_integral hInt
    (tendsto_neg_atTop_atBot.comp hLtop) hLtop
  have hsum := hdiff.add hT
  simp only [zero_add] at hsum
  exact hsum.congr fun n ↦ sub_add_cancel (P n) (T n)

private theorem canonicalProfile_const_mul (lam : ℝ) (c : ℂ) (g : ℝ → ℂ) (s : ℝ) :
    canonicalProfile lam (fun t ↦ c * g t) s = c * canonicalProfile lam g s := by
  simp only [canonicalProfile, profileIntegrand, deriv_const_mul_field', mul_assoc,
    integral_const_mul]
  ring

private theorem integral_arc_pairing_eq {lam : ℝ} {κ : ℂ} {U : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℂ}
    (hU : closure cellSquare ⊆ U) (hκ : κ = 1 ∨ κ = -1 ∨ κ = I ∨ κ = -I)
    (hUR : ∀ p ∈ U, (p.2, -p.1) ∈ U) (hfR : ∀ p ∈ U, f (p.2, -p.1) = κ * f p) (k : ℕ) :
    (∫ s, (canonicalProfile lam (f ∘ cellArc k) s * conj (f (cellArc k s))).re) =
      ∫ s, (canonicalProfile lam (f ∘ separatrixArc) s * conj (f (separatrixArc s))).re := by
  have hArc : f ∘ cellArc k = fun s ↦ (κ : ℂ) ^ k * (f ∘ separatrixArc) s := by
    funext s
    exact apply_rotLift_iterate hUR hfR
      (hU (arcSegment_subset_closure_cellSquare (separatrixArc_mem_arcSegment s))) k
  have hunit : (κ : ℂ) * conj (κ : ℂ) = 1 := by
    rcases hκ with rfl | rfl | rfl | rfl <;> simp [← pow_two, Complex.I_sq]
  have hpow : (κ : ℂ) ^ k * conj ((κ : ℂ) ^ k) = 1 := by
    rw [map_pow, ← mul_pow, hunit, one_pow]
  change (∫ s, (canonicalProfile lam (f ∘ cellArc k) s * conj ((f ∘ cellArc k) s)).re) = _
  rw [hArc]
  apply integral_congr_ae
  filter_upwards with s
  rw [canonicalProfile_const_mul, map_mul]
  calc
    _ = (((κ : ℂ) ^ k * conj ((κ : ℂ) ^ k)) *
        (canonicalProfile lam (f ∘ separatrixArc) s * conj ((f ∘ separatrixArc) s))).re := by
      congr 1
      ring
    _ = _ := by rw [hpow, one_mul]; rfl

set_option maxHeartbeats 1200000 in
-- Assemble the representative changes, periodic integral identities and quarter limit.
/-- For any common good sequence carrying the specified ACL transports, the
vorticity pairing converges to the four canonical arc pairings. Keeping the
sequence as input permits use on several rotation components at once. -/
theorem pairing_limit_character_of_goodLevels {lam : ℝ} {κ : ℂ}
    {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hU : closure cellSquare ⊆ U)
    (hκ : κ = 1 ∨ κ = -1 ∨ κ = I ∨ κ = -I)
    (hUR : ∀ p ∈ U, (p.2, -p.1) ∈ U) (hfR : ∀ p ∈ U, f (p.2, -p.1) = κ * f p)
    (hfc : ContinuousOn f U) {hs : ℕ → ℝ}
    (hhs : ∀ n, hs n ∈ Ioo 0 1 ∧
      ∃ m : ℤ, |lam * orbitPeriod (hs n) - 2 * Real.pi * (m + 1 / 2)| < Real.pi / 3)
    (hlim : Tendsto hs atTop (𝓝 0)) {Z : ℕ → ℝ → ℂ}
    (hZ : ∀ n, (∀ᵐ t, Z n t = transportUnknown lam v f (dipoleOrbit (hs n) t)) ∧
      (∀ a b, AbsolutelyContinuousOnInterval (Z n) a b) ∧
      (∀ᵐ t, HasDerivAt (Z n) (I * (lam * Z n t + f (dipoleOrbit (hs n) t))) t) ∧
      ∀ t, Z n (t + 2 * eighthPeriod (hs n)) = κ * Z n t) :
    Tendsto (fun n ↦ levelIntegral (hs n) (fun p ↦ (v p * conj (f p)).re)) atTop
      (𝓝 (∑ k ∈ Finset.range 4, ∫ s, (canonicalProfile lam (f ∘ cellArc k) s *
        conj (f (cellArc k s))).re)) := by
  have hchar (n : ℕ) : Z n (eighthPeriod (hs n)) = κ * Z n (-eighthPeriod (hs n)) := by
    have h := (hZ n).2.2.2 (-eighthPeriod (hs n))
    simpa only [show -eighthPeriod (hs n) + 2 * eighthPeriod (hs n) = eighthPeriod (hs n)
      by ring] using h
  have hq := quarter_pairing_limit hp hU hκ hUR hfR hfc
    (fun n ↦ ⟨(hhs n).1, (hhs n).2⟩) hlim
    (fun n ↦ (hZ n).2.1) (fun n ↦ (hZ n).2.2.1) hchar
  have hfull (n : ℕ) : levelIntegral (hs n) (fun p ↦ (v p * conj (f p)).re) =
      4 * ∫ t in (-eighthPeriod (hs n))..eighthPeriod (hs n),
        ((-(lam : ℂ) * Z n t - f (dipoleOrbit (hs n) t)) *
          conj (f (dipoleOrbit (hs n) t))).re := by
    let G : ℝ → ℂ := fun t ↦ f (dipoleOrbit (hs n) t)
    let V : ℝ → ℂ := fun t ↦ -(lam : ℂ) * Z n t - G t
    let Q : ℝ → ℝ := fun t ↦ (V t * conj (G t)).re
    have hGc : Continuous G := hfc.comp_continuous
      (continuous_dipoleOrbit.comp (continuous_const.prodMk continuous_id))
      (fun t ↦ hU (subset_closure (dipoleOrbit_mem_cellSquare (hhs n).1.1 (hhs n).1.2 t)))
    have hZc := continuous_of_absolutelyContinuous (hZ n).2.1
    have hQc : Continuous Q := by dsimp only [Q, V]; fun_prop
    have hGchar (t : ℝ) : G (t + 2 * eighthPeriod (hs n)) = κ * G t := by
      dsimp only [G]
      rw [dipoleOrbit_add_quarter (hhs n).1.1 (hhs n).1.2]
      exact hfR _ (hU (subset_closure (dipoleOrbit_mem_cellSquare (hhs n).1.1 (hhs n).1.2 t)))
    have hVchar (t : ℝ) : V (t + 2 * eighthPeriod (hs n)) = κ * V t := by
      dsimp only [V]
      rw [(hZ n).2.2.2 t, hGchar]
      ring
    have hunit : (κ : ℂ) * conj (κ : ℂ) = 1 := by
      rcases hκ with rfl | rfl | rfl | rfl <;> simp [← pow_two, Complex.I_sq]
    have hper : Function.Periodic Q (2 * eighthPeriod (hs n)) := by
      intro t
      dsimp only [Q]
      rw [hVchar, hGchar, map_mul]
      calc
        _ = (((κ : ℂ) * conj (κ : ℂ)) * (V t * conj (G t))).re := by congr 1; ring
        _ = _ := by rw [hunit, one_mul]
    have hv : V =ᵐ[volume] fun t ↦ v (dipoleOrbit (hs n) t) := by
      filter_upwards [(hZ n).1] with t ht
      dsimp only [V]
      rw [ht, transportUnknown]
      dsimp only [G]
      field_simp [ofReal_ne_zero.2 hp.ne_zero]
      ring
    have heq : levelIntegral (hs n) (fun p ↦ (v p * conj (f p)).re) =
        ∫ t in (0 : ℝ)..orbitPeriod (hs n), Q t := by
      unfold levelIntegral
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hv] with t ht _
      dsimp only [Q, G]
      rw [ht]
    rw [heq, orbitPeriod]
    change (∫ t in (0 : ℝ)..8 * eighthPeriod (hs n), Q t) =
      4 * ∫ t in (-eighthPeriod (hs n))..eighthPeriod (hs n), Q t
    have h4 := hper.intervalIntegral_add_zsmul_eq 4 0 fun a b ↦ hQc.intervalIntegrable a b
    have hshift := hper.intervalIntegral_add_eq 0 (-eighthPeriod (hs n))
    rw [show 8 * eighthPeriod (hs n) = 0 + (4 : ℤ) • (2 * eighthPeriod (hs n))
      by simp; ring, h4, zsmul_eq_mul, hshift,
      show -eighthPeriod (hs n) + 2 * eighthPeriod (hs n) = eighthPeriod (hs n) by ring]
    norm_num
  have harcs : (∑ k ∈ Finset.range 4, ∫ s, (canonicalProfile lam (f ∘ cellArc k) s *
      conj (f (cellArc k s))).re) =
      4 * ∫ s, (canonicalProfile lam (f ∘ separatrixArc) s * conj (f (separatrixArc s))).re := by
    simp_rw [integral_arc_pairing_eq hU hκ hUR hfR]
    simp
  rw [harcs]
  exact (hq.const_mul 4).congr fun n ↦ (hfull n).symm

/-- The limit of the vorticity pairing for any of the four rotation characters.
The good sequence can avoid an arbitrary prescribed null set. -/
theorem pairing_limit_character {lam : ℝ} {κ : ℂ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hU : closure cellSquare ⊆ U) (hκ : κ = 1 ∨ κ = -1 ∨ κ = I ∨ κ = -I)
    (hUR : ∀ p ∈ U, (p.2, -p.1) ∈ U) (hfR : ∀ p ∈ U, f (p.2, -p.1) = κ * f p)
    (hfc : ContinuousOn f U)
    {N : Set ℝ} (hN : volume N = 0) :
    ∃ hs : ℕ → ℝ, (∀ j, hs j ∈ Set.Ioo 0 1 ∧ hs j ∉ N ∧
        ∃ m : ℤ, |lam * orbitPeriod (hs j) - 2 * Real.pi * (m + 1 / 2)| < Real.pi / 3) ∧
      Tendsto hs atTop (𝓝 0) ∧
      Tendsto (fun j ↦ levelIntegral (hs j) (fun p ↦ (v p * (starRingEnd ℂ) (f p)).re)) atTop
        (𝓝 (∑ k ∈ Finset.range 4, ∫ s, (canonicalProfile lam (f ∘ cellArc k) s *
          (starRingEnd ℂ) (f (cellArc k s))).re)) := by
  obtain ⟨hs, Z, hhs, hlim, hZ⟩ := hp.exists_goodLevels_transport
    (subset_closure.trans hU) (κ := κ) (fun p hp ↦ hfR p hp) hN
  exact ⟨hs, hhs, hlim, pairing_limit_character_of_goodLevels hp hU hκ hUR hfR hfc
    (fun n ↦ ⟨(hhs n).1, (hhs n).2.2⟩) hlim (Z := Z)
    (fun n ↦ ⟨(hZ n).1, (hZ n).2.2⟩)⟩

/-- The real-character specialization used in the equal-parity sectors. -/
theorem pairing_limit {lam κ : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hU : closure cellSquare ⊆ U) (hκ : κ = 1 ∨ κ = -1)
    (hUR : ∀ p ∈ U, (p.2, -p.1) ∈ U) (hfR : ∀ p ∈ U, f (p.2, -p.1) = κ * f p)
    (hfc : ContinuousOn f U)
    {N : Set ℝ} (hN : volume N = 0) :
    ∃ hs : ℕ → ℝ, (∀ j, hs j ∈ Set.Ioo 0 1 ∧ hs j ∉ N ∧
        ∃ m : ℤ, |lam * orbitPeriod (hs j) - 2 * Real.pi * (m + 1 / 2)| < Real.pi / 3) ∧
      Tendsto hs atTop (𝓝 0) ∧
      Tendsto (fun j ↦ levelIntegral (hs j) (fun p ↦ (v p * (starRingEnd ℂ) (f p)).re)) atTop
        (𝓝 (∑ k ∈ Finset.range 4, ∫ s, (canonicalProfile lam (f ∘ cellArc k) s *
          (starRingEnd ℂ) (f (cellArc k s))).re)) := by
  apply pairing_limit_character hp hU _ hUR hfR hfc hN
  rcases hκ with rfl | rfl <;> simp


/-- Melnikov and pairing traces specialized to raw eigenfunction lifts and continuous arc
    traces, with no admitted dependencies. -/
theorem ee_transport_traces {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (_hs : InSector true true ω) {κ : Bool}
    (hκ : InRotationCharacter κ ω) :
    (∀ k < 4, Integrable (deriv (contStream ω ∘ cellArc k))) ∧
    ∀ N : Set ℝ, volume N = 0 → ∃ hs : ℕ → ℝ,
      (∀ j, hs j ∈ Ioo 0 1 ∧ hs j ∉ N) ∧ Tendsto hs atTop (𝓝 0) ∧
      Tendsto (fun j ↦ levelIntegral (hs j) fun p ↦
        (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re) atTop
        (𝓝 (∑ k ∈ Finset.range 4, ∫ s,
          (canonicalProfile lam (contStream ω ∘ cellArc k) s *
            (starRingEnd ℂ) (contStream ω (cellArc k s))).re)) := by
  let c : ℝ := if κ then 1 else -1
  have hc : c = 1 ∨ c = -1 := by cases κ <;> simp [c]
  have hcc : (c : ℂ) = paritySign κ := by cases κ <;> simp [c, paritySign]
  have hU := isOrbitUnion_cellNeighbourhood
  have hp := isTransportPair_contStream hlam hω hU isBounded_cellNeighbourhood
  have hfR : ∀ p ∈ cellNeighbourhood, contStream ω (p.2, -p.1) = c * contStream ω p := by
    intro p _
    rw [hcc]
    exact contStream_rotLift hκ p
  have hUR : ∀ p ∈ cellNeighbourhood, (p.2, -p.1) ∈ cellNeighbourhood :=
    fun _ hp ↦ rotLift_mem_cellNeighbourhood hp
  refine ⟨fun k _ ↦ (ee_melnikov hlam hω hκ k).1, ?_⟩
  · intro N hN
    have hvm : Measurable (liftL2 ω) := (Lp.stronglyMeasurable ω).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable
    have hfm : Measurable (streamLift ω) := (Lp.stronglyMeasurable (invLap ω)).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable
    have hcm := (continuous_contStream ω).measurable
    have hraw : Measurable (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re) := by
      fun_prop
    have hcont : Measurable (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (contStream ω p)).re) := by
      fun_prop
    have hrep : (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re) =ᵐ[volume]
        (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (contStream ω p)).re) := by
      filter_upwards [streamLift_ae_eq_contStream ω] with p hp
      rw [hp]
    have hlevels := ae_levelIntegral_congr hraw hcont hrep
    let Nr : Set ℝ := {h | h ∈ Ioo 0 1 ∧ levelIntegral h
      (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re) ≠ levelIntegral h
      (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (contStream ω p)).re)}
    have hNr : volume Nr = 0 := by
      have hh := (ae_restrict_iff' measurableSet_Ioo).1 hlevels
      simpa only [ae_iff, not_imp] using hh
    obtain ⟨seq, hseq, hlim, hpair⟩ := pairing_limit hp
      closure_cellSquare_subset_cellNeighbourhood hc hUR hfR
      (continuous_contStream ω).continuousOn (hN := measure_union_null hN hNr)
    refine ⟨seq, fun j ↦ ⟨(hseq j).1, fun hj ↦ (hseq j).2.1 (Or.inl hj)⟩, hlim, ?_⟩
    apply hpair.congr
    intro j
    have heq : levelIntegral (seq j)
        (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (streamLift ω p)).re) = levelIntegral (seq j)
        (fun p ↦ (liftL2 ω p * (starRingEnd ℂ) (contStream ω p)).re) := by
      by_contra hj
      exact (hseq j).2.1 (Or.inr ⟨(hseq j).1, hj⟩)
    exact heq.symm


end NoEmbeddedEigenvalues
