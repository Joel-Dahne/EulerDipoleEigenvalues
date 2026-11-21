module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.TransversalMollifier
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.ACLSlicing
public import NoEmbeddedEigenvalues.Transport.PeriodicComparison.TransportODE

/-!
# Restriction to almost every orbit

Blueprint: `lem:coarea`.

If `L₀g = Lg` weakly on an open set containing an orbit annulus, then on almost every orbit
`g ∘ γ_h` has a periodic, locally absolutely continuous representative with derivative
`Lg ∘ γ_h`. The proof uses no coarea formula and no approximation:

* Cut off with `χ(h)`, equal to `1` on an interior level band `[a, b]`. Since `L₀` kills
  functions of the level, the cut-off pair satisfies the weak transport equation on the whole
  punctured cell (`HasWeakL0On.levelCutoff`).
* In action-angle coordinates this is the weak angular derivative `∂_θ U = S(h) K` on the strip
  (`hasWeakL0On_iff_actionAngle`). Directional ACL slicing (`lem:acl-slicing`) gives sections
  that are locally absolutely continuous in `θ` for almost every `h`.
* The sections are `1`-periodic: they are continuous and agree almost everywhere with the
  pointwise periodic pullback. Rescaling `θ = t / S(h)` gives flow time.
* Countably many bands exhaust `(h₁, h₂)`.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Complex
open scoped Topology ContDiff

/-- `L₀(χ(Ψ)) = 0`, since `Ψ` is constant along the flow. -/
theorem classicalL0_ofReal_comp_dipoleLift {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ)
    (p : ℝ × ℝ) : classicalL0 (fun q ↦ (χ (dipoleLift q) : ℂ)) p = 0 := by
  have hx : partialX (fun q ↦ (χ (dipoleLift q) : ℂ)) p =
      ((deriv χ (dipoleLift p) * -Real.sin p.1 : ℝ) : ℂ) := by
    have h := ((hχ (dipoleLift p)).hasDerivAt.comp p.1
      ((Real.hasDerivAt_cos p.1).add_const (Real.cos p.2))).ofReal_comp
    exact h.deriv
  have hy : partialY (fun q ↦ (χ (dipoleLift q) : ℂ)) p =
      ((deriv χ (dipoleLift p) * -Real.sin p.2 : ℝ) : ℂ) := by
    have h := ((hχ (dipoleLift p)).hasDerivAt.comp p.2
      ((Real.hasDerivAt_cos p.2).const_add (Real.cos p.1))).ofReal_comp
    exact h.deriv
  simp only [classicalL0, hx, hy, Complex.real_smul]
  push_cast
  ring

/-- Multiplication by a smooth function of the level commutes with `L₀`. -/
theorem classicalL0_levelMul {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {φ : ℝ × ℝ → ℂ}
    (hφ : Differentiable ℝ φ) (p : ℝ × ℝ) :
    classicalL0 (fun q ↦ (χ (levelCoord q) : ℂ) * φ q) p =
      (χ (levelCoord p) : ℂ) * classicalL0 φ p := by
  have hχ' : Differentiable ℝ (fun s ↦ χ (s / 2)) :=
    (hχ.differentiable (by simp)).comp (differentiable_id.div_const 2)
  have hc : Differentiable ℝ (fun q ↦ (χ (levelCoord q) : ℂ)) := by
    have : Differentiable ℝ (fun q : ℝ × ℝ ↦ dipoleLift q) := by unfold dipoleLift; fun_prop
    exact Complex.ofRealCLM.differentiable.comp (hχ'.comp this)
  have h0 := classicalL0_ofReal_comp_dipoleLift hχ' p
  have hlev : (fun q ↦ (χ (dipoleLift q / 2) : ℂ)) = fun q ↦ (χ (levelCoord q) : ℂ) := rfl
  rw [hlev] at h0
  simp only [classicalL0, partialX_mul (hc p) (hφ p), partialY_mul (hc p) (hφ p),
    Complex.real_smul] at h0 ⊢
  linear_combination φ p * h0

theorem isOpen_puncturedCell' : IsOpen puncturedCell := by
  have h₁ : Continuous (fun q : ℝ × ℝ ↦ |(diagCoord q).1|) := by unfold diagCoord; fun_prop
  have h₂ : Continuous (fun q : ℝ × ℝ ↦ |(diagCoord q).2|) := by unfold diagCoord; fun_prop
  exact ((isOpen_lt h₁ continuous_const).inter (isOpen_lt h₂ continuous_const)).sdiff
    isClosed_singleton

/-- A level cutoff supported inside `(h₁, h₂)` turns weak transport on a neighbourhood of the
orbit annulus into weak transport on the whole punctured cell. -/
theorem HasWeakL0On.levelCutoff {U : Set (ℝ × ℝ)} {g Lg : ℝ × ℝ → ℂ} {h₁ h₂ : ℝ}
    (hA : orbitAnnulus h₁ h₂ ⊆ U) (hd : HasWeakL0On U g Lg) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo h₁ h₂) :
    HasWeakL0On puncturedCell (fun p ↦ (χ (levelCoord p) : ℂ) * g p)
      (fun p ↦ (χ (levelCoord p) : ℂ) * Lg p) := by
  have hl : Continuous levelCoord := by unfold levelCoord dipoleLift; fun_prop
  set c : ℝ × ℝ → ℂ := fun p ↦ (χ (levelCoord p) : ℂ) with hc_def
  have hcs : ContDiff ℝ ∞ c :=
    Complex.ofRealCLM.contDiff.comp (hχ.comp (by unfold levelCoord dipoleLift; fun_prop))
  have hcz (p : ℝ × ℝ) (hp : levelCoord p ∉ tsupport χ) : c p = 0 := by
    simp [hc_def, image_eq_zero_of_notMem_tsupport hp]
  have htc : tsupport c ⊆ levelCoord ⁻¹' tsupport χ :=
    closure_minimal (fun p hp ↦ by_contra fun h ↦ hp (hcz p h))
      ((isClosed_tsupport χ).preimage hl)
  -- Local integrability on the punctured cell.
  have hloc {v : ℝ × ℝ → ℂ} (hv : LocallyIntegrableOn v U) :
      LocallyIntegrableOn (fun p ↦ c p * v p) puncturedCell := by
    refine (locallyIntegrableOn_iff isOpen_puncturedCell'.isLocallyClosed).2 fun K hKs hK ↦ ?_
    set K' := K ∩ levelCoord ⁻¹' tsupport χ
    have hK' : IsCompact K' := hK.inter_right ((isClosed_tsupport χ).preimage hl)
    have hK'U : K' ⊆ U := fun p hp ↦ hA ⟨hKs hp.1, hχs hp.2⟩
    have hi : IntegrableOn (fun p ↦ c p * v p) K' :=
      (hv.integrableOn_compact_subset hK'U hK').continuousOn_mul hcs.continuous.continuousOn hK'
    refine hi.of_forall_sdiff_eq_zero hK.measurableSet fun p hp ↦ ?_
    simp [hcz p fun h ↦ hp.2 ⟨hp.1, h⟩]
  refine ⟨hloc hd.1, hloc hd.2.1, fun φ hφ ↦ ?_⟩
  have hψ : IsTestFunctionOn U (fun p ↦ c p * φ p) := by
    refine ⟨hcs.mul hφ.contDiff, hφ.hasCompactSupport.mul_left, fun p hp ↦ hA ?_⟩
    have hp1 := tsupport_mul_subset_left (f := c) (g := φ) hp
    have hp2 := tsupport_mul_subset_right (f := c) (g := φ) hp
    exact ⟨hφ.tsupport_subset hp2, hχs (htc hp1)⟩
  have hw := hd.2.2 _ hψ
  rw [show classicalL0 (fun p ↦ c p * φ p) = fun p ↦ c p * classicalL0 φ p from
    funext (classicalL0_levelMul hχ (hφ.contDiff.differentiable (by simp)))] at hw
  change ∫ p, c p * g p * classicalL0 φ p = -∫ p, c p * Lg p * φ p
  have e1 : (fun p ↦ c p * g p * classicalL0 φ p) = fun p ↦ g p * (c p * classicalL0 φ p) := by
    funext p; ring
  have e2 : (fun p ↦ c p * Lg p * φ p) = fun p ↦ Lg p * (c p * φ p) := by
    funext p; ring
  rw [e1, e2]
  exact hw

/-- The orbit restriction on an interior level band `(a, b)`. -/
theorem ae_orbit_restriction_band {U : Set (ℝ × ℝ)} {g Lg : ℝ × ℝ → ℂ} {h₁ h₂ a b : ℝ}
    (h₁0 : 0 < h₁) (h₂1 : h₂ < 1) (ha : h₁ < a) (hab : a < b) (hb : b < h₂)
    (hA : orbitAnnulus h₁ h₂ ⊆ U) (hd : HasWeakL0On U g Lg) :
    ∀ᵐ h ∂(volume.restrict (Ioo a b)), ∃ G : ℝ → ℂ,
      (∀ᵐ t, G t = g (dipoleOrbit h t)) ∧ Function.Periodic G (orbitPeriod h) ∧
      (∀ c d, AbsolutelyContinuousOnInterval G c d) ∧
      ∀ᵐ t, HasDerivAt G (Lg (dipoleOrbit h t)) t := by
  -- A level cutoff equal to `1` on `[a, b]`.
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_Ioo (a := (h₁ + a) / 2) (b := (b + h₂) / 2)) (isClosed_Icc (a := a) (b := b))
    (fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hχt : tsupport χ ⊆ Ioo h₁ h₂ := by
    rw [tsupport, hχs, closure_Ioo (by linarith)]
    exact Icc_subset_Ioo (by linarith) (by linarith)
  -- The angular weak derivative on the band, and its ACL representative.
  have hloc := (hd.levelCutoff hA hχ hχt).comp_actionAngleInv
  have hsub : Ioo a b ×ˢ (univ : Set ℝ) ⊆ actionStrip :=
    prod_mono (Ioo_subset_Ioo (by linarith) (by linarith)) subset_rfl
  obtain ⟨G, -, hGeq, hacl⟩ := (hloc.mono hsub).exists_acl_sections isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.2 hab) isOpen_univ ordConnected_univ univ_nonempty
  have hm : volume.restrict (Ioo a b ×ˢ (univ : Set ℝ)) =
      (volume.restrict (Ioo a b)).prod volume := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [hm] at hGeq
  have hfub := Measure.ae_ae_of_ae_prod hGeq
  filter_upwards [hacl, hacl.ae_continuousOn isOpen_univ, hfub, ae_restrict_mem measurableSet_Ioo]
    with h ⟨hac, hder⟩ hcont hfu hh
  have h0 : 0 < h := by linarith [hh.1]
  have h1 : h < 1 := by linarith [hh.2]
  set S := orbitPeriod h with hS_def
  have hS : 0 < S := orbitPeriod_pos h0 h1
  have hc1 (θ : ℝ) : (χ (levelCoord (actionAngleInv (h, θ))) : ℂ) = 1 := by
    rw [levelCoord_actionAngleInv h0 h1, (hχ1 h).1 (Ioo_subset_Icc_self hh)]
    simp
  set F : ℝ → ℂ := fun θ ↦ G (h, θ) with hF_def
  have hcF : Continuous F := continuousOn_univ.1 hcont
  have hfu' : ∀ᵐ θ, F θ = g (actionAngleInv (h, θ)) := by
    filter_upwards [hfu] with θ hθ
    change G (h, θ) = _
    rw [hθ]
    simp only [Function.comp_apply, hc1, one_mul]
  rw [Measure.restrict_univ] at hder
  have hder' : ∀ᵐ θ, HasDerivAt F ((S : ℂ) * Lg (actionAngleInv (h, θ))) θ := by
    filter_upwards [hder] with θ hθ
    convert hθ using 1
    simp only [hc1, one_mul, hS_def]
  -- The sections are `1`-periodic.
  have hper (θ : ℝ) : F (θ + 1) = F θ := by
    have hae : (fun θ ↦ F (θ + 1)) =ᵐ[volume] F := by
      have h2 := (measurePreserving_add_right volume (1 : ℝ)).quasiMeasurePreserving.ae hfu'
      filter_upwards [h2, hfu'] with θ h2 h3
      rw [h2, h3, actionAngleInv_add_one h0 h1]
    have hc1 : Continuous fun θ ↦ F (θ + 1) := hcF.comp (continuous_id.add continuous_const)
    exact congrFun ((hc1.ae_eq_iff_eq volume hcF).1 hae) θ
  -- Rescale to flow time.
  have hq : QuasiMeasurePreserving (fun t : ℝ ↦ t / S) volume volume := by
    simpa only [smul_eq_mul, div_eq_inv_mul] using
      Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (inv_ne_zero hS.ne')
  have hinv (t : ℝ) : actionAngleInv (h, t / S) = dipoleOrbit h t := by
    simp only [actionAngleInv]
    rw [div_mul_cancel₀ t hS.ne']
  refine ⟨fun t ↦ F (t / S), ?_, fun t ↦ ?_, fun c d ↦ ?_, ?_⟩
  · filter_upwards [hq.ae hfu'] with t ht
    rw [ht, hinv]
  · simp only
    rw [add_div, div_self hS.ne', hper]
  · have hL : LipschitzOnWith (Real.toNNReal S⁻¹) (fun t : ℝ ↦ t / S) (uIcc c d) := by
      refine (LipschitzWith.of_dist_le_mul fun x y ↦ le_of_eq ?_).lipschitzOnWith
      rw [Real.dist_eq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hS,
        Real.coe_toNNReal _ (inv_nonneg.2 hS.le), div_eq_inv_mul]
    have hmono : MonotoneOn (fun t : ℝ ↦ t / S) (uIcc c d) :=
      fun x _ y _ hxy ↦ div_le_div_of_nonneg_right hxy hS.le
    have hmaps : MapsTo (fun t : ℝ ↦ t / S) (uIcc c d) (uIcc (c / S) (d / S)) := by
      intro x hx
      rw [mem_uIcc] at hx ⊢
      rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
      · exact Or.inl ⟨div_le_div_of_nonneg_right hx1 hS.le, div_le_div_of_nonneg_right hx2 hS.le⟩
      · exact Or.inr ⟨div_le_div_of_nonneg_right hx1 hS.le, div_le_div_of_nonneg_right hx2 hS.le⟩
    exact AbsolutelyContinuousOnInterval.comp_monotoneOn (hac (c / S) (d / S) (subset_univ _))
      hL hmono hmaps
  · filter_upwards [hq.ae hder'] with t ht
    have h2 := ht.scomp t ((hasDerivAt_id t).div_const S)
    refine h2.congr_deriv ?_
    rw [hinv, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, one_div_mul_cancel hS.ne',
      Complex.ofReal_one, one_mul]

/-- Restriction to almost every orbit (`lem:coarea`): if `L₀g = h` weakly on an open set
    containing an orbit annulus, then on almost every orbit `g ∘ γ_h` agrees a.e. with a
    periodic, locally absolutely continuous function whose derivative in flow time is
    `h ∘ γ_h`. -/
theorem ae_orbit_restriction {U : Set (ℝ × ℝ)} {g Lg : ℝ × ℝ → ℂ} {h₁ h₂ : ℝ}
    (h₁0 : 0 < h₁) (h₁₂ : h₁ < h₂) (h₂1 : h₂ < 1) (hA : orbitAnnulus h₁ h₂ ⊆ U)
    (hd : HasWeakL0On U g Lg) :
    ∀ᵐ h ∂(volume.restrict (Set.Ioo h₁ h₂)), ∃ G : ℝ → ℂ,
      (∀ᵐ t, G t = g (dipoleOrbit h t)) ∧ Function.Periodic G (orbitPeriod h) ∧
      (∀ c d, AbsolutelyContinuousOnInterval G c d) ∧
      ∀ᵐ t, HasDerivAt G (Lg (dipoleOrbit h t)) t := by
  set δ := h₂ - h₁
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hcover : Ioo h₁ h₂ = ⋃ n : ℕ, Ioo (h₁ + δ / (n + 3)) (h₂ - δ / (n + 3)) := by
    ext h
    simp only [mem_Ioo, mem_iUnion]
    constructor
    · rintro ⟨hh1, hh2⟩
      set m := min (h - h₁) (h₂ - h)
      have hm : 0 < m := lt_min (by linarith) (by linarith)
      obtain ⟨n, hn⟩ := exists_nat_gt (δ / m)
      have hn' := (div_lt_iff₀ hm).1 hn
      have hlt : δ / (n + 3) < m := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      exact ⟨n, by linarith [min_le_left (h - h₁) (h₂ - h)],
        by linarith [min_le_right (h - h₁) (h₂ - h)]⟩
    · rintro ⟨n, hh1, hh2⟩
      have : 0 < δ / (n + 3) := by positivity
      exact ⟨by linarith, by linarith⟩
  rw [hcover, ae_restrict_iUnion_iff]
  intro n
  have hpos : 0 < δ / (n + 3) := by positivity
  have hhalf : δ / (n + 3) < δ / 2 :=
    div_lt_div_of_pos_left hδ (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  exact ae_orbit_restriction_band h₁0 h₂1 (by linarith) (by simp only [δ] at hhalf ⊢; linarith)
    (by linarith) hA hd

end NoEmbeddedEigenvalues
