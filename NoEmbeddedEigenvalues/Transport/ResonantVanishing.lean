module

public import NoEmbeddedEigenvalues.EvenEven.TraceExclusion.EigenfunctionTransport
public import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.IntervalH1
public import NoEmbeddedEigenvalues.Transport.PeriodicComparison.TransportODE
public import NoEmbeddedEigenvalues.Analysis.OrbitRestriction.OrbitRestriction

/-!
# Orbitwise transport and resonant vanishing

Blueprint: `lem:resonant-vanishing`, `lem:cell-orbit-transport`,
`lem:good-level-transport`.

On almost every orbit `γ_h` of an annulus, the transport unknown `z` of a transport pair is a
periodic absolutely continuous solution of `(-i∂ₜ - λ)z = f`. Integrating
`(e^{-ikbt} z)'` over one period gives the mode relation `(kb - λ) v_k = -kb f_k`.
At a resonance `kb(h_k) = λ` the right side must vanish: otherwise `|v_k(h)| ≳ 1/|h - h_k|`,
which is not locally integrable in `h`, contradicting the local L¹ bound from the area
formula. Only the local Lipschitz bound `|kb(h) - λ| ≤ C|h - h_k|` enters, not the sign of
`S'` or square integrability of `v`.

Rational annuli give one common full-measure set of cell levels carrying transport
representatives. Good levels avoiding any prescribed null set can be selected there.
At those levels periodic uniqueness transfers the forcing's quarter-period character
to the representatives; no planar a.e. character hypothesis on `v` is needed. The results,
including the orbit-restriction prerequisite `lem:coarea`, have no admitted dependencies.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Complex
open scoped Topology

/-! ### One orbit -/

section Orbit

/-- Absolutely continuous complex functions have interval-integrable a.e. derivatives. -/
theorem intervalIntegrable_of_absolutelyContinuous {Z D : ℝ → ℂ} {a b : ℝ}
    (hZ : AbsolutelyContinuousOnInterval Z a b)
    (hD : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt Z (D t) t) : IntervalIntegrable D volume a b := by
  have hr : AbsolutelyContinuousOnInterval (fun x ↦ (Z x).re) a b := by
    simpa using! reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hZ
  have hi : AbsolutelyContinuousOnInterval (fun x ↦ (Z x).im) a b := by
    simpa using! imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hZ
  have hre : IntervalIntegrable (fun t ↦ (D t).re) volume a b := by
    refine hr.intervalIntegrable_deriv.congr_ae ((ae_restrict_iff' measurableSet_uIoc).2 ?_)
    filter_upwards [hD] with t ht htI
    simpa using! (reCLM.hasFDerivAt.comp_hasDerivAt t (ht (uIoc_subset_uIcc htI))).deriv
  have him : IntervalIntegrable (fun t ↦ (D t).im) volume a b := by
    refine hi.intervalIntegrable_deriv.congr_ae ((ae_restrict_iff' measurableSet_uIoc).2 ?_)
    filter_upwards [hD] with t ht htI
    simpa using! (imCLM.hasFDerivAt.comp_hasDerivAt t (ht (uIoc_subset_uIcc htI))).deriv
  have hD' : D = fun t ↦ ((D t).re : ℂ) + I * ((D t).im : ℂ) := by
    funext t
    rw [mul_comm]
    exact (re_add_im (D t)).symm
  rw [hD', intervalIntegrable_iff]
  exact (intervalIntegrable_iff.1 hre).ofReal.add
    ((intervalIntegrable_iff.1 him).ofReal.const_mul I)

/-- The mode identity on one orbit. If `Z` is `S`-periodic and absolutely continuous with
`Z' = i(λZ + F)` almost everywhere, and `bS = 2π`, then `F` is integrable over a period and
`(kb - λ) ∫₀^S e^{-ikbt} Z = ∫₀^S e^{-ikbt} F`. -/
theorem integral_exp_mul_transport {S b lam : ℝ} (hbS : b * S = 2 * Real.pi) {Z F : ℝ → ℂ}
    (hper : Function.Periodic Z S) (hac : AbsolutelyContinuousOnInterval Z 0 S)
    (hd : ∀ᵐ t, HasDerivAt Z (I * (lam * Z t + F t)) t) (k : ℤ) :
    IntervalIntegrable F volume 0 S ∧
      (k * b - lam) * ∫ t in (0 : ℝ)..S, exp (-(I * k * b * t)) * Z t =
        ∫ t in (0 : ℝ)..S, exp (-(I * k * b * t)) * F t := by
  obtain ⟨e, he_def⟩ : ∃ e : ℝ → ℂ, e = fun t : ℝ ↦ exp (-(I * k * b * (t : ℂ))) := ⟨_, rfl⟩
  suffices H : IntervalIntegrable F volume 0 S ∧
      (k * b - lam) * ∫ t in (0 : ℝ)..S, e t * Z t = ∫ t in (0 : ℝ)..S, e t * F t by
    simpa only [he_def] using H
  have hlin : ContDiff ℝ 1 (fun t : ℝ ↦ -(I * k * b * (t : ℂ))) :=
    (contDiff_const.mul ofRealCLM.contDiff).neg
  have hecd : ContDiff ℝ 1 e := he_def ▸ Complex.contDiff_exp.comp hlin
  have he (t : ℝ) : HasDerivAt e (-(I * k * b) * e t) t := by
    have h1 : HasDerivAt (fun s : ℝ ↦ -(I * k * b * (s : ℂ))) (-(I * k * b)) t := by
      have := ((hasDerivAt_id t).ofReal_comp.const_mul (I * k * b)).neg
      simpa [Pi.neg_def, Function.comp_def] using this
    rw [he_def]
    simpa only [mul_comm] using h1.cexp
  have hec : Continuous e := hecd.continuous
  have hZD : IntervalIntegrable (fun t ↦ I * (lam * Z t + F t)) volume 0 S :=
    intervalIntegrable_of_absolutelyContinuous hac (hd.mono fun t ht _ ↦ ht)
  have hZc : IntervalIntegrable Z volume 0 S := hac.continuousOn.intervalIntegrable
  have hF : IntervalIntegrable F volume 0 S := by
    have hFe : F = fun t ↦ -I * (I * (lam * Z t + F t)) - lam * Z t := by
      funext t
      ring_nf
      rw [I_sq]
      ring
    rw [hFe]
    exact (hZD.const_mul _).sub (hZc.const_mul _)
  refine ⟨hF, ?_⟩
  have heac : AbsolutelyContinuousOnInterval e 0 S :=
    hecd.contDiffOn.absolutelyContinuousOnInterval
  have hW : AbsolutelyContinuousOnInterval (fun t ↦ e t * Z t) 0 S := heac.fun_smul hac
  have hDi : IntervalIntegrable (fun t ↦ -(I * k * b) * (e t * Z t) + e t * (I * (lam * Z t + F t)))
      volume 0 S :=
    ((hZc.continuousOn_mul hec.continuousOn).const_mul _).add
      (hZD.continuousOn_mul hec.continuousOn)
  have hderiv : ∀ᵐ t, t ∈ uIcc 0 S → HasDerivAt (fun t ↦ e t * Z t)
      (-(I * k * b) * (e t * Z t) + e t * (I * (lam * Z t + F t))) t := by
    filter_upwards [hd] with t ht _
    exact ((he t).mul ht).congr_deriv (by ring)
  have hFTC := complex_integral_eq_sub_of_ac hW hDi hderiv
  have heS : e S = 1 := by
    rw [he_def]
    have hc : -(I * k * b * S) = ((-k : ℤ) : ℂ) * (2 * Real.pi * I) := by
      have : ((b : ℂ) * S) = 2 * Real.pi := by exact_mod_cast hbS
      push_cast
      linear_combination (-(I * k)) * this
    simp only
    rw [hc, exp_int_mul_two_pi_mul_I]
  have he0 : e 0 = 1 := by simp [he_def]
  have hZS : Z S = Z 0 := by simpa using hper 0
  rw [heS, he0, hZS] at hFTC
  have hi1 : IntervalIntegrable (fun t ↦ e t * Z t) volume 0 S :=
    hZc.continuousOn_mul hec.continuousOn
  have hi2 : IntervalIntegrable (fun t ↦ e t * F t) volume 0 S :=
    hF.continuousOn_mul hec.continuousOn
  have hsplit : ∫ t in (0 : ℝ)..S, (-(I * k * b) * (e t * Z t) + e t * (I * (lam * Z t + F t))) =
      (I * (lam - k * b)) * (∫ t in (0 : ℝ)..S, e t * Z t) +
        I * ∫ t in (0 : ℝ)..S, e t * F t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _)]
    congr 1
    funext t
    ring
  rw [hsplit] at hFTC
  have := mul_left_cancel₀ I_ne_zero (show I * ((lam - k * b) * (∫ t in (0 : ℝ)..S, e t * Z t) +
      ∫ t in (0 : ℝ)..S, e t * F t) = I * 0 by linear_combination hFTC)
  linear_combination -this

end Orbit

/-! ### Almost every orbit -/

section Modes

variable {lam : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}

/-- On almost every orbit of the annulus the transport unknown solves `(-i∂ₜ - λ)z = f`. -/
theorem IsTransportPair.ae_orbit_transport (hp : IsTransportPair lam U v f) {h₁ h₂ : ℝ}
    (h₁0 : 0 < h₁) (h₁₂ : h₁ < h₂) (h₂1 : h₂ < 1) (hA : orbitAnnulus h₁ h₂ ⊆ U) :
    ∀ᵐ h ∂(volume.restrict (Set.Ioo h₁ h₂)), ∃ Z : ℝ → ℂ,
      (∀ᵐ t, Z t = transportUnknown lam v f (dipoleOrbit h t)) ∧
      Function.Periodic Z (orbitPeriod h) ∧ (∀ c d, AbsolutelyContinuousOnInterval Z c d) ∧
      ∀ᵐ t, HasDerivAt Z (I * (lam * Z t + f (dipoleOrbit h t))) t := by
  filter_upwards [ae_orbit_restriction h₁0 h₁₂ h₂1 hA
    hp.hasWeakL0On_transportUnknown_sub] with h ⟨G, hG, hper, hac, hd⟩
  refine ⟨G, hG, hper, hac, ?_⟩
  filter_upwards [hd, hG] with t ht hGt
  rwa [← hGt] at ht

/-- A single full-measure set of levels carries periodic ACL transport representatives
    throughout the cell. Countably many rational annuli suffice, so no uncountable union
    of exceptional sets is taken. -/
theorem IsTransportPair.ae_orbit_transport_cell (hp : IsTransportPair lam U v f)
    (hU : cellSquare ⊆ U) :
    ∀ᵐ h ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), ∃ Z : ℝ → ℂ,
      (∀ᵐ t, Z t = transportUnknown lam v f (dipoleOrbit h t)) ∧
      Function.Periodic Z (orbitPeriod h) ∧ (∀ c d, AbsolutelyContinuousOnInterval Z c d) ∧
      ∀ᵐ t, HasDerivAt Z (I * (lam * Z t + f (dipoleOrbit h t))) t := by
  let P : ℝ → Prop := fun h ↦ ∃ Z : ℝ → ℂ,
    (∀ᵐ t, Z t = transportUnknown lam v f (dipoleOrbit h t)) ∧
    Function.Periodic Z (orbitPeriod h) ∧ (∀ c d, AbsolutelyContinuousOnInterval Z c d) ∧
    ∀ᵐ t, HasDerivAt Z (I * (lam * Z t + f (dipoleOrbit h t))) t
  have hq (a b : ℚ) : ∀ᵐ h : ℝ, 0 < (a : ℝ) → (a : ℝ) < b → (b : ℝ) < 1 →
      h ∈ Set.Ioo (a : ℝ) b → P h := by
    by_cases ha : 0 < (a : ℝ)
    · by_cases hab : (a : ℝ) < b
      · by_cases hb : (b : ℝ) < 1
        · have hA : orbitAnnulus a b ⊆ U := fun p hp ↦ hU hp.1.1
          filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1
            (hp.ae_orbit_transport ha hab hb hA)] with h hh _ _ _ hmem
          exact hh hmem
        · exact ae_of_all _ fun _ _ _ hb' ↦ (hb hb').elim
      · exact ae_of_all _ fun _ _ hab' ↦ (hab hab').elim
    · exact ae_of_all _ fun _ ha' ↦ (ha ha').elim
  have hall : ∀ᵐ h : ℝ, ∀ a b : ℚ, 0 < (a : ℝ) → (a : ℝ) < b → (b : ℝ) < 1 →
      h ∈ Set.Ioo (a : ℝ) b → P h :=
    ae_all_iff.2 fun a ↦ ae_all_iff.2 fun b ↦ hq a b
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_Ioo] with h hh hh01
  obtain ⟨a, ha0, hah⟩ := exists_rat_btwn hh01.1
  obtain ⟨b, hhb, hb1⟩ := exists_rat_btwn hh01.2
  exact hh a b ha0 (hah.trans hhb) hb1 ⟨hah, hhb⟩

/-- Good levels avoiding a prescribed null set carry periodic ACL representatives of
    the transport unknown with the forcing's quarter-period character. The character
    follows from nonresonant periodic uniqueness, not an a.e. rotation identity for `v`. -/
theorem IsTransportPair.exists_goodLevels_transport (hp : IsTransportPair lam U v f)
    (hU : cellSquare ⊆ U) {κ : ℂ} (hfR : ∀ p ∈ U, f (rotLift p) = κ * f p)
    {N : Set ℝ} (hN : volume N = 0) :
    ∃ (hs : ℕ → ℝ) (Z : ℕ → ℝ → ℂ),
      (∀ j, hs j ∈ Set.Ioo 0 1 ∧ hs j ∉ N ∧
        ∃ m : ℤ, |lam * orbitPeriod (hs j) - 2 * Real.pi * (m + 1 / 2)| < Real.pi / 3) ∧
      Tendsto hs atTop (𝓝 0) ∧
      ∀ j, (∀ᵐ t, Z j t = transportUnknown lam v f (dipoleOrbit (hs j) t)) ∧
        Function.Periodic (Z j) (orbitPeriod (hs j)) ∧
        (∀ c d, AbsolutelyContinuousOnInterval (Z j) c d) ∧
        (∀ᵐ t, HasDerivAt (Z j) (I * (lam * Z j t + f (dipoleOrbit (hs j) t))) t) ∧
        ∀ t, Z j (t + 2 * eighthPeriod (hs j)) = κ * Z j t := by
  obtain ⟨hs, hhs, hlim⟩ := exists_goodLevels_avoiding hp.ne_zero
    (hp.ae_orbit_transport_cell hU) hN
  have hZ (j : ℕ) := (hhs j).2.2.2.1
  choose Z hrep hper hac hd using hZ
  refine ⟨hs, Z, fun j ↦ ⟨(hhs j).1, (hhs j).2.2.1, (hhs j).2.2.2.2⟩, hlim, ?_⟩
  intro j
  refine ⟨hrep j, hper j, hac j, hd j, ?_⟩
  obtain ⟨m, hm⟩ := (hhs j).2.2.2.2
  refine transport_character_of_periodic
    (orbitPeriod_pos (hhs j).1.1 (hhs j).1.2)
    (exp_orbitPeriod_ne_one_of_goodWindow hm) (hper j) (hac j) (hd j) ?_
  intro t
  rw [dipoleOrbit_add_quarter (hhs j).1.1 (hhs j).1.2]
  exact hfR _ (hU (dipoleOrbit_mem_cellSquare (hhs j).1.1 (hhs j).1.2 t))

/-- The mode relation `(kb - λ) v_k = -kb f_k` on almost every orbit, for all `k`. -/
theorem IsTransportPair.ae_mode_relation (hp : IsTransportPair lam U v f) {h₁ h₂ : ℝ}
    (h₁0 : 0 < h₁) (h₁₂ : h₁ < h₂) (h₂1 : h₂ < 1) (hA : orbitAnnulus h₁ h₂ ⊆ U) :
    ∀ᵐ h ∂(volume.restrict (Set.Ioo h₁ h₂)), ∀ k : ℤ,
      (k * orbitFrequency h - lam) * angularMode h k v =
        -(k * orbitFrequency h) * angularMode h k f := by
  have hl : (lam : ℂ) ≠ 0 := ofReal_ne_zero.2 hp.ne_zero
  filter_upwards [hp.ae_orbit_transport h₁0 h₁₂ h₂1 hA, ae_restrict_mem measurableSet_Ioo]
    with h ⟨Z, hZ, hper, hac, hd⟩ hh k
  have hS : 0 < orbitPeriod h := orbitPeriod_pos (h₁0.trans hh.1) (hh.2.trans h₂1)
  have hbS : orbitFrequency h * orbitPeriod h = 2 * Real.pi := by
    unfold orbitFrequency
    field_simp
  obtain ⟨hFi, hmode⟩ := integral_exp_mul_transport hbS hper (hac 0 _) hd k
  set e : ℝ → ℂ := fun t ↦ exp (-(I * k * orbitFrequency h * t))
  have hec : Continuous e := by simp only [e]; fun_prop
  have hi1 : IntervalIntegrable (fun t ↦ e t * Z t) volume 0 (orbitPeriod h) :=
    (hac 0 _).continuousOn.intervalIntegrable.continuousOn_mul hec.continuousOn
  have hi2 : IntervalIntegrable (fun t ↦ e t * f (dipoleOrbit h t)) volume 0 (orbitPeriod h) :=
    hFi.continuousOn_mul hec.continuousOn
  have hv : ∫ t in (0 : ℝ)..orbitPeriod h, e t * v (dipoleOrbit h t) =
      -lam * (∫ t in (0 : ℝ)..orbitPeriod h, e t * Z t) -
        ∫ t in (0 : ℝ)..orbitPeriod h, e t * f (dipoleOrbit h t) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (hi1.const_mul _) hi2]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hZ] with t ht _
    rw [ht]
    simp only [transportUnknown]
    field_simp
    ring
  unfold angularMode
  change (k * orbitFrequency h - lam) * ((orbitPeriod h : ℂ)⁻¹ *
      ∫ t in (0 : ℝ)..orbitPeriod h, e t * v (dipoleOrbit h t)) =
    -(k * orbitFrequency h) * ((orbitPeriod h : ℂ)⁻¹ *
      ∫ t in (0 : ℝ)..orbitPeriod h, e t * f (dipoleOrbit h t))
  rw [hv]
  linear_combination (-lam * (orbitPeriod h : ℂ)⁻¹) * hmode

end Modes

/-! ### Continuity of the modes -/

section Continuity

/-- The angular mode in normalized time: `g_k(h) = ∫₀¹ e^{-2πikθ} g(γ_h(θ S(h))) dθ`. -/
theorem angularMode_eq_integral_angle {h : ℝ} (h0 : 0 < h) (h1 : h < 1) (k : ℤ)
    (g : ℝ × ℝ → ℂ) :
    angularMode h k g = ∫ θ in (0 : ℝ)..1,
      exp (-(2 * Real.pi * I * k * θ)) * g (actionAngleInv (h, θ)) := by
  have hS := orbitPeriod_pos h0 h1
  have hbS : ((orbitFrequency h : ℂ) * (orbitPeriod h : ℂ)) = 2 * Real.pi := by
    have : orbitFrequency h * orbitPeriod h = 2 * Real.pi := by
      unfold orbitFrequency
      field_simp
    exact_mod_cast this
  have hc := intervalIntegral.integral_comp_mul_right
    (fun t : ℝ ↦ exp (-(I * k * orbitFrequency h * t)) * g (dipoleOrbit h t)) hS.ne'
    (a := 0) (b := 1)
  simp only [zero_mul, one_mul, real_smul, ofReal_inv] at hc
  unfold angularMode
  rw [← hc]
  refine intervalIntegral.integral_congr fun θ _ ↦ ?_
  simp only [actionAngleInv]
  congr 2
  push_cast
  linear_combination (-(I * k * θ)) * hbS

/-- The modes of a function continuous on a neighbourhood of an annulus are continuous in the
level. -/
theorem continuousAt_angularMode {U : Set (ℝ × ℝ)} {g : ℝ × ℝ → ℂ} (hg : ContinuousOn g U)
    {h₁ h₂ : ℝ} (h₁0 : 0 < h₁) (h₂1 : h₂ < 1) (hA : orbitAnnulus h₁ h₂ ⊆ U) (k : ℤ)
    {h₀ : ℝ} (hh₀ : h₀ ∈ Ioo h₁ h₂) : ContinuousAt (fun h ↦ angularMode h k g) h₀ := by
  set δ := min (h₀ - h₁) (h₂ - h₀) / 2
  have hδ : 0 < δ := by have := hh₀.1; have := hh₀.2; positivity
  have hδ1 : h₁ < h₀ - δ := by
    have := min_le_left (h₀ - h₁) (h₂ - h₀); simp only [δ]; linarith [hh₀.1]
  have hδ2 : h₀ + δ < h₂ := by
    have := min_le_right (h₀ - h₁) (h₂ - h₀); simp only [δ]; linarith [hh₀.2]
  set c : ℝ → ℝ := fun h ↦ max (h₀ - δ) (min (h₀ + δ) h)
  have hc : Continuous c := by fun_prop
  have hcI (h : ℝ) : c h ∈ Ioo h₁ h₂ :=
    ⟨hδ1.trans_le (le_max_left _ _),
      (max_le (by linarith) (min_le_left _ _)).trans_lt hδ2⟩
  have hcI' (h : ℝ) : c h ∈ Ioo (0 : ℝ) 1 := ⟨h₁0.trans (hcI h).1, (hcI h).2.trans h₂1⟩
  have hcnear : ∀ᶠ h in 𝓝 h₀, c h = h := by
    filter_upwards [Ioo_mem_nhds (show h₀ - δ < h₀ by linarith) (show h₀ < h₀ + δ by linarith)]
      with h hh
    simp only [c, min_eq_right hh.2.le, max_eq_right hh.1.le]
  have hSc : Continuous fun h ↦ orbitPeriod (c h) :=
    continuousOn_orbitPeriod.comp_continuous hc hcI'
  have hAA : Continuous fun q : ℝ × ℝ ↦ actionAngleInv (c q.1, q.2) :=
    continuous_dipoleOrbit.comp ((hc.comp continuous_fst).prodMk
      (continuous_snd.mul (hSc.comp continuous_fst)))
  have hmem (q : ℝ × ℝ) : actionAngleInv (c q.1, q.2) ∈ U :=
    hA ⟨actionAngleInv_mem_puncturedCell (hcI' q.1).1 (hcI' q.1).2 q.2, by
      rw [levelCoord_actionAngleInv (hcI' q.1).1 (hcI' q.1).2]; exact hcI q.1⟩
  have hG : Continuous fun q : ℝ × ℝ ↦
      exp (-(2 * Real.pi * I * k * q.2)) * g (actionAngleInv (c q.1, q.2)) :=
    (by fun_prop : Continuous fun q : ℝ × ℝ ↦ exp (-(2 * Real.pi * I * k * q.2))).mul
      (hg.comp_continuous hAA hmem)
  have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun h θ ↦ exp (-(2 * Real.pi * I * k * θ)) * g (actionAngleInv (c h, θ)))
    (μ := volume) hG 0 1
  refine hcont.continuousAt.congr ?_
  filter_upwards [hcnear] with h hh
  rw [hh, angularMode_eq_integral_angle (hh ▸ hcI' h).1 (hh ▸ hcI' h).2]

end Continuity

/-! ### Integrability of the modes in the level -/

section Integrability

theorem measurable_actionAngleInv : Measurable actionAngleInv :=
  continuous_dipoleOrbit.measurable.comp (measurable_fst.prodMk
    (measurable_snd.mul ((measurable_eighthPeriod.const_mul 8).comp measurable_fst)))

theorem measurableSet_orbitAnnulus (h₁ h₂ : ℝ) : MeasurableSet (orbitAnnulus h₁ h₂) := by
  have hc : MeasurableSet cellSquare := by
    unfold cellSquare diagCoord
    exact ((isOpen_lt (by fun_prop : Continuous fun p : ℝ × ℝ ↦ |(p.1 + p.2) / 2|)
      continuous_const).inter (isOpen_lt
        (by fun_prop : Continuous fun p : ℝ × ℝ ↦ |(p.1 - p.2) / 2|)
          continuous_const)).measurableSet
  have hl : Measurable levelCoord := by
    unfold levelCoord dipoleLift
    fun_prop
  exact (hc.diff (measurableSet_singleton 0)).inter (hl measurableSet_Ioo)

theorem volume_orbitAnnulus_lt_top (h₁ h₂ : ℝ) : volume (orbitAnnulus h₁ h₂) < ⊤ := by
  refine (measure_mono (t := Icc (-Real.pi) Real.pi ×ˢ Icc (-Real.pi) Real.pi)
    fun p hp ↦ ?_).trans_lt (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  obtain ⟨h1, h2⟩ := hp.1.1
  simp only [diagCoord, abs_lt] at h1 h2
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- `|g_k(h)| ≤ ∫_{-1/4}^{3/4} |g(γ_h(θ S(h)))| dθ`. -/
theorem enorm_angularMode_le {h : ℝ} (h0 : 0 < h) (h1 : h < 1) (k : ℤ) (g : ℝ × ℝ → ℂ) :
    ‖angularMode h k g‖ₑ ≤ ∫⁻ θ in Ico (-1 / 4 : ℝ) (3 / 4), ‖g (actionAngleInv (h, θ))‖ₑ := by
  rw [angularMode_eq_integral_angle h0 h1]
  have hper : Function.Periodic
      (fun θ : ℝ ↦ exp (-(2 * Real.pi * I * k * θ)) * g (actionAngleInv (h, θ))) 1 := by
    intro θ
    simp only [actionAngleInv_add_one h0 h1]
    congr 1
    have : -(2 * Real.pi * I * k * ((θ + 1 : ℝ) : ℂ)) =
        -(2 * Real.pi * I * k * θ) + ((-k : ℤ) : ℂ) * (2 * Real.pi * I) := by
      push_cast
      ring
    rw [this, exp_add, exp_int_mul_two_pi_mul_I, mul_one]
  have hshift := hper.intervalIntegral_add_eq 0 (-1 / 4)
  rw [zero_add, show (-1 / 4 : ℝ) + 1 = 3 / 4 by norm_num] at hshift
  rw [hshift, intervalIntegral.integral_of_le (by norm_num),
    setLIntegral_congr (Ico_ae_eq_Ioc (μ := volume))]
  refine (eNorm_integral_le_lintegral_eNorm _).trans (le_of_eq ?_)
  congr 1
  funext θ
  have hn : ‖exp (-(2 * Real.pi * I * k * θ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [eNorm_mul, ← ofReal_norm, hn, ENNReal.ofReal_one, one_mul]

/-- The modes of a function in `L²` of a neighbourhood of an annulus are integrable in the
level: `∫ |v_k(h)| dh < ∞`. The proof changes `v` on a null set to a measurable function,
which changes the restrictions to almost every orbit only on null sets of the angle, and
then uses `dx dy = 2S(h) dh dθ`. -/
theorem lintegral_enorm_angularMode_lt_top {U : Set (ℝ × ℝ)} {v : ℝ × ℝ → ℂ}
    (hv : MemLp v 2 (volume.restrict U)) {h₁ h₂ : ℝ} (h₁0 : 0 < h₁) (h₁₂ : h₁ < h₂)
    (h₂1 : h₂ < 1) (hA : orbitAnnulus h₁ h₂ ⊆ U) (k : ℤ) :
    ∫⁻ h in Ioo h₁ h₂, ‖angularMode h k v‖ₑ < ⊤ := by
  set A := orbitAnnulus h₁ h₂
  have hAm := measurableSet_orbitAnnulus h₁ h₂
  have hAc : A ⊆ cellSquare := fun p hp ↦ hp.1.1
  set v' := hv.aestronglyMeasurable.mk v
  have hv'm : StronglyMeasurable v' := hv.aestronglyMeasurable.stronglyMeasurable_mk
  have hvv' : ∀ᵐ p ∂(volume.restrict A), v p = v' p :=
    ae_restrict_of_ae_restrict_of_subset hA hv.aestronglyMeasurable.ae_eq_mk
  -- A measurable null set outside which `v = v'` on the annulus.
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null
    (s := {p | p ∈ A ∧ v p ≠ v' p}) (by
      have := (ae_restrict_iff' hAm).1 hvv'
      rw [ae_iff] at this
      refine measure_mono_null (fun p hp ↦ ?_) this
      exact fun h ↦ hp.2 (h hp.1))
  -- The levels of the strip where the orbit meets `N` in positive measure form a null set.
  have hG : Measurable fun q : ℝ × ℝ ↦
      ENNReal.ofReal (2 * orbitPeriod q.1) * N.indicator 1 (actionAngleInv q) :=
    (ENNReal.measurable_ofReal.comp (((measurable_eighthPeriod.const_mul 8).const_mul 2).comp
      measurable_fst)).mul ((measurable_one.indicator hNm).comp measurable_actionAngleInv)
  have hcell := lintegral_cellSquare_actionAngle (measurable_one.indicator hNm)
  have hzero : ∫⁻ p in cellSquare, N.indicator 1 p = 0 :=
    le_antisymm ((setLIntegral_le_lintegral _ _).trans (by
      rw [lintegral_indicator_one hNm, hN0])) bot_le
  rw [hzero, eq_comm, lintegral_eq_zero_iff (hG.lintegral_prod_right')] at hcell
  have hgood : ∀ᵐ h ∂(volume.restrict (Ioo h₁ h₂)), ‖angularMode h k v‖ₑ ≤
      ∫⁻ θ in Ico (-1 / 4 : ℝ) (3 / 4), ‖v' (actionAngleInv (h, θ))‖ₑ := by
    have hsub : Ioo h₁ h₂ ⊆ Ioo 0 1 := Ioo_subset_Ioo h₁0.le h₂1.le
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hcell,
      ae_restrict_mem measurableSet_Ioo] with h hh hhI
    have h0 : 0 < h := h₁0.trans hhI.1
    have h1 : h < 1 := hhI.2.trans h₂1
    refine (enorm_angularMode_le h0 h1 k v).trans (le_of_eq (lintegral_congr_ae ?_))
    have hS : ENNReal.ofReal (2 * orbitPeriod h) ≠ 0 := by
      have := orbitPeriod_pos h0 h1
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hθ := (lintegral_eq_zero_iff ((hG.comp measurable_prodMk_left))).1 hh
    filter_upwards [hθ] with θ hθ
    simp only [Function.comp_apply, Pi.zero_apply, mul_eq_zero, hS, false_or,
      indicator_apply_eq_zero, Pi.one_apply, one_ne_zero, imp_false] at hθ
    have hmem : actionAngleInv (h, θ) ∈ A :=
      ⟨actionAngleInv_mem_puncturedCell h0 h1 θ, by rw [levelCoord_actionAngleInv h0 h1]; exact hhI⟩
    by_contra hne
    exact hθ (hNsub ⟨hmem, fun he ↦ hne (by rw [he])⟩)
  -- A lower bound for the period on the annulus.
  have h₂0 : 0 < h₂ := h₁0.trans h₁₂
  set Smin := 4 * Real.log (1 / h₂)
  have hSmin : 0 < Smin := by
    have : 1 < 1 / h₂ := by rw [lt_div_iff₀ h₂0]; linarith
    have := Real.log_pos this
    positivity
  have hSle : ∀ h ∈ Ioo h₁ h₂, Smin ≤ orbitPeriod h := by
    intro h hh
    have h0 : 0 < h := h₁0.trans hh.1
    have hL := log_le_eighthPeriod h0 (hh.2.trans h₂1)
    have hl : Real.log (1 / h₂) ≤ Real.log (1 / h) :=
      Real.log_le_log (by positivity) (one_div_le_one_div_of_le h0 hh.2.le)
    unfold orbitPeriod
    simp only [Smin]
    linarith
  set c := ENNReal.ofReal (2 * Smin)⁻¹
  set w : ℝ × ℝ → ENNReal := A.indicator fun p ↦ ‖v' p‖ₑ
  have hw : Measurable w := hv'm.measurable.eNorm.indicator hAm
  have hpt : ∀ h ∈ Ioo h₁ h₂, ∀ θ, ‖v' (actionAngleInv (h, θ))‖ₑ ≤
      c * (ENNReal.ofReal (2 * orbitPeriod h) * w (actionAngleInv (h, θ))) := by
    intro h hh θ
    have h0 : 0 < h := h₁0.trans hh.1
    have h1 : h < 1 := hh.2.trans h₂1
    have hmem : actionAngleInv (h, θ) ∈ A :=
      ⟨actionAngleInv_mem_puncturedCell h0 h1 θ, by rw [levelCoord_actionAngleInv h0 h1]; exact hh⟩
    have hS := orbitPeriod_pos h0 h1
    rw [show w (actionAngleInv (h, θ)) = ‖v' (actionAngleInv (h, θ))‖ₑ from
      indicator_of_mem hmem _, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    have h1le : 1 ≤ (2 * Smin)⁻¹ * (2 * orbitPeriod h) := by
      rw [le_inv_mul_iff₀ (by positivity)]
      linarith [hSle h hh]
    calc ‖v' (actionAngleInv (h, θ))‖ₑ = 1 * ‖v' (actionAngleInv (h, θ))‖ₑ := (one_mul _).symm
      _ ≤ _ := mul_le_mul_left (ENNReal.one_le_ofReal.2 h1le) _
  have hfin : ∫⁻ p in A, ‖v' p‖ₑ < ⊤ := by
    have hm : MemLp v' 2 (volume.restrict A) :=
      (hv.ae_eq hv.aestronglyMeasurable.ae_eq_mk).mono_measure (Measure.restrict_mono hA le_rfl)
    have : IsFiniteMeasure (volume.restrict A) :=
      isFiniteMeasure_restrict.2 (volume_orbitAnnulus_lt_top h₁ h₂).ne
    exact (memLp_one_iff_integrable.1 (hm.mono_exponent (by norm_num))).2
  calc ∫⁻ h in Ioo h₁ h₂, ‖angularMode h k v‖ₑ
      ≤ ∫⁻ h in Ioo h₁ h₂, ∫⁻ θ in Ico (-1 / 4 : ℝ) (3 / 4), ‖v' (actionAngleInv (h, θ))‖ₑ :=
        lintegral_mono_ae hgood
    _ ≤ ∫⁻ h in Ioo h₁ h₂, c * ∫⁻ θ in Ico (-1 / 4 : ℝ) (3 / 4),
          ENNReal.ofReal (2 * orbitPeriod h) * w (actionAngleInv (h, θ)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_mono fun θ ↦ hpt h hh θ
    _ = c * ∫⁻ h in Ioo h₁ h₂, ∫⁻ θ in Ico (-1 / 4 : ℝ) (3 / 4),
          ENNReal.ofReal (2 * orbitPeriod h) * w (actionAngleInv (h, θ)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ c * ∫⁻ h in Ioo 0 1, ∫⁻ θ in Ico (-1 / 4 : ℝ) (3 / 4),
          ENNReal.ofReal (2 * orbitPeriod h) * w (actionAngleInv (h, θ)) := by
        gcongr
    _ = c * ∫⁻ p in cellSquare, w p := by rw [lintegral_cellSquare_actionAngle hw]
    _ = c * ∫⁻ p in A, ‖v' p‖ₑ := by
        rw [lintegral_indicator hAm, Measure.restrict_restrict hAm, inter_eq_left.2 hAc]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end Integrability

/-! ### Resonant vanishing -/

section Resonance

variable {lam : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}

/-- At a resonant level `kb(h_k) = λ` the mode `f_k(h_k)` vanishes, if `f` is continuous.
Otherwise the mode relation gives `|v_k(h)| ≥ c/(h - h_k)` just above `h_k`, using only
`|kb(h) - λ| ≤ C|h - h_k|`, and `1/(h - h_k)` is not integrable. -/
theorem IsTransportPair.angularMode_eq_zero_of_resonant (hp : IsTransportPair lam U v f)
    {h₁ h₂ : ℝ} (h₁0 : 0 < h₁) (h₁₂ : h₁ < h₂) (h₂1 : h₂ < 1) (hA : orbitAnnulus h₁ h₂ ⊆ U)
    (hfc : ContinuousOn f U) (k : ℤ) {hk : ℝ} (hkI : hk ∈ Ioo h₁ h₂)
    (hres : k * orbitFrequency hk = lam) : angularMode hk k f = 0 := by
  by_contra hne
  have hk0 : 0 < hk := h₁0.trans hkI.1
  have hk1 : hk < 1 := hkI.2.trans h₂1
  have hlam : lam ≠ 0 := hp.ne_zero
  -- The frequency is differentiable at `h_k`.
  set β : ℝ → ℝ := fun h ↦ k * orbitFrequency h
  have hSd : DifferentiableAt ℝ orbitPeriod hk :=
    (deriv_eighthPeriod_neg hk0 hk1).1.const_mul (8 : ℝ)
  have hβd : DifferentiableAt ℝ β hk :=
    ((differentiableAt_const _).div hSd (orbitPeriod_pos hk0 hk1).ne').const_mul _
  obtain ⟨C, hC⟩ := hβd.hasDerivAt.isBigO_sub.bound
  set C' := max C 1
  have hC' : 0 < C' := lt_max_of_lt_right one_pos
  -- Near `h_k`: Lipschitz bound, `|β| ≥ |λ|/2`, `|f_k| ≥ |f_k(h_k)|/2`, inside the annulus.
  set m := ‖angularMode hk k f‖
  have hm : 0 < m := norm_pos_iff.2 hne
  have hβc : ∀ᶠ h in 𝓝 hk, |lam| / 2 < |β h| := by
    have : |β hk| = |lam| := by simp only [β, hres]
    exact (hβd.continuousAt.abs).eventually (lt_mem_nhds (by
      change |lam| / 2 < |β hk|
      rw [this]; linarith [abs_pos.2 hlam]))
  have hfk : ∀ᶠ h in 𝓝 hk, m / 2 < ‖angularMode h k f‖ :=
    (continuousAt_angularMode hfc h₁0 h₂1 hA k hkI).norm.eventually (lt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    (hC.and (hβc.and (hfk.and (Ioo_mem_nhds hkI.1 hkI.2))))
  set δ' := min δ 1 / 2
  have hδ' : 0 < δ' := by positivity
  have hδδ : δ' < δ := by have := min_le_left δ 1; simp only [δ']; linarith
  have hnear (h : ℝ) (hh : h ∈ Ioc hk (hk + δ')) : dist h hk < δ := by
    rw [Real.dist_eq, abs_of_pos (by linarith [hh.1])]
    linarith [hh.2]
  have hIsub : Ioc hk (hk + δ') ⊆ Ioo h₁ h₂ := fun h hh ↦ (hball (hnear h hh)).2.2.2
  -- The lower bound `|v_k(h)| ≥ c₀/(C'(h - h_k))` almost everywhere just above `h_k`.
  set c₀ := |lam| / 2 * (m / 2)
  have hc₀ : 0 < c₀ := by have := abs_pos.2 hlam; positivity
  have hlow : ∀ᵐ h ∂(volume.restrict (Ioc hk (hk + δ'))),
      ENNReal.ofReal (c₀ / C') * ENNReal.ofReal (h - hk)⁻¹ ≤ ‖angularMode h k v‖ₑ := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hIsub
      (hp.ae_mode_relation h₁0 h₁₂ h₂1 hA), ae_restrict_mem measurableSet_Ioc] with h hrel hh
    obtain ⟨hL, hβh, hfh, -⟩ := hball (hnear h hh)
    have hpos : 0 < h - hk := by linarith [hh.1]
    have hrel' := congrArg norm (hrel k)
    rw [norm_mul, norm_mul, norm_neg] at hrel'
    have e1 : ‖((k : ℂ) * orbitFrequency h - lam)‖ = |β h - β hk| := by
      rw [show β hk = lam from hres, show ((k : ℂ) * orbitFrequency h - lam) =
        ((β h - lam : ℝ) : ℂ) by simp only [β]; push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs]
    have e2 : ‖((k : ℂ) * orbitFrequency h)‖ = |β h| := by
      rw [show ((k : ℂ) * orbitFrequency h) = ((β h : ℝ) : ℂ) by simp only [β]; push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [e1, e2] at hrel'
    have hL' : |β h - β hk| ≤ C' * (h - hk) := by
      have := hL
      simp only [Real.norm_eq_abs, abs_of_pos hpos] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le)
    have hprod : c₀ ≤ C' * (h - hk) * ‖angularMode h k v‖ := by
      calc c₀ ≤ |β h| * ‖angularMode h k f‖ := by
            apply mul_le_mul hβh.le hfh.le (by positivity) (abs_nonneg _)
        _ = |β h - β hk| * ‖angularMode h k v‖ := hrel'.symm
        _ ≤ C' * (h - hk) * ‖angularMode h k v‖ :=
            mul_le_mul_of_nonneg_right hL' (norm_nonneg _)
    rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [div_mul_eq_mul_div, div_le_iff₀ hC', ← div_eq_mul_inv, div_le_iff₀ hpos]
    nlinarith [hprod]
  -- Integrate.
  have hfin := lintegral_enorm_angularMode_lt_top hp.memLp h₁0 h₁₂ h₂1 hA k
  have hI : ∫⁻ h in Ioc hk (hk + δ'), ENNReal.ofReal (h - hk)⁻¹ < ⊤ := by
    have h1 : ENNReal.ofReal (c₀ / C') * ∫⁻ h in Ioc hk (hk + δ'), ENNReal.ofReal (h - hk)⁻¹ < ⊤ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ((lintegral_mono_ae hlow).trans (lintegral_mono_set hIsub)).trans_lt hfin
    exact (ENNReal.mul_lt_top_iff.1 h1).elim (fun h ↦ h.2) (fun h ↦ h.elim
      (fun h0 ↦ absurd h0 (by simp only [ENNReal.ofReal_eq_zero, not_le]; positivity))
      (fun h0 ↦ by rw [h0]; exact ENNReal.zero_lt_top))
  have hint : IntervalIntegrable (fun h ↦ (h - hk)⁻¹) volume hk (hk + δ') := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    refine ⟨(measurable_id.sub_const _).inv.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal]
    · exact hI
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
      exact inv_nonneg.2 (by linarith [hh.1])
  rw [intervalIntegrable_sub_inv_iff] at hint
  rcases hint with h | h
  · linarith
  · exact h (left_mem_uIcc)

/-! ### The lemma -/

/-- Orbitwise transport and resonant vanishing (`lem:resonant-vanishing`). On almost every orbit
    of an annulus the transport unknown solves `(-i∂ₜ - λ)z = f`, the angular modes satisfy
    `(k b(h) - λ) v_k = -k b(h) f_k`, and if `f` is continuous then `f_k` vanishes at every
    resonant level `k b(h_k) = λ`. -/
theorem resonant_vanishing {lam : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) {h₁ h₂ : ℝ} (h₁0 : 0 < h₁) (h₁₂ : h₁ < h₂) (h₂1 : h₂ < 1)
    (hA : orbitAnnulus h₁ h₂ ⊆ U) :
    (∀ᵐ h ∂(volume.restrict (Set.Ioo h₁ h₂)), ∃ Z : ℝ → ℂ,
      (∀ᵐ t, Z t = transportUnknown lam v f (dipoleOrbit h t)) ∧
      Function.Periodic Z (orbitPeriod h) ∧ (∀ c d, AbsolutelyContinuousOnInterval Z c d) ∧
      ∀ᵐ t, HasDerivAt Z (I * (lam * Z t + f (dipoleOrbit h t))) t) ∧
    (∀ᵐ h ∂(volume.restrict (Set.Ioo h₁ h₂)), ∀ k : ℤ,
      (k * orbitFrequency h - lam) * angularMode h k v =
        -(k * orbitFrequency h) * angularMode h k f) ∧
    (ContinuousOn f U → ∀ k : ℤ, ∀ hk ∈ Set.Ioo h₁ h₂, k * orbitFrequency hk = lam →
      angularMode hk k f = 0) :=
  ⟨hp.ae_orbit_transport h₁0 h₁₂ h₂1 hA, hp.ae_mode_relation h₁0 h₁₂ h₂1 hA,
    fun hfc k _ hkI hres ↦ hp.angularMode_eq_zero_of_resonant h₁0 h₁₂ h₂1 hA hfc k hkI hres⟩

end Resonance

end NoEmbeddedEigenvalues
