import NoEmbeddedEigenvalues.Analysis.LocalSobolev.IntervalIntegralFlux
import NoEmbeddedEigenvalues.Transport.WeightedGains.WeightedNumeratorData

/-!
# The weak moving-endpoint derivative of the quarter numerator

Blueprint: `lem:orbit-window-flux`, `lem:numerator-moving-endpoints`.

Normalized orbit time makes the integration window fixed. The change of
period contributes a transverse divergence; its integral is exactly the two
moving-endpoint values of the original continuous forcing. This cancellation
leaves the fixed-time orbit-level derivative in the bulk, with no differentiated
ray value of the weak gradient.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Real
open scoped Topology ContDiff

/-- The candidate moving-endpoint derivative, using the specified weak gradient. -/
def quarterNumeratorDerivative (lam : ℝ) (g : ℝ × ℝ → ℂ)
    (D : List (Fin 2) → ℝ × ℝ → ℂ) (h : ℝ) : ℂ :=
  (∫ t in (-eighthPeriod h)..eighthPeriod h,
    quarterForcingLevelDerivative D (h, t) * Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))) +
  ((deriv eighthPeriod h : ℝ) : ℂ) *
    (g (dipoleOrbit h (eighthPeriod h)) *
       Complex.exp (-Complex.I * ((lam * eighthPeriod h : ℝ) : ℂ)) +
     g (dipoleOrbit h (-eighthPeriod h)) *
       Complex.exp (-Complex.I * ((lam * (-eighthPeriod h) : ℝ) : ℂ)))

private def phase (lam : ℝ) (q : ℝ × ℝ) : ℂ :=
  Complex.exp (-Complex.I * ((lam * (q.2 * orbitPeriod q.1) : ℝ) : ℂ))

private def weight (lam : ℝ) (q : ℝ × ℝ) : ℂ := (orbitPeriod q.1 : ℂ) * phase lam q

private def fluxWeight (lam : ℝ) (q : ℝ × ℝ) : ℂ := (q.2 : ℂ) * phase lam q

private def chartGradient (D : List (Fin 2) → ℝ × ℝ → ℂ) (j : Fin 2)
    (q : ℝ × ℝ) : ℂ :=
  ((coordPartial j (fun q ↦ (actionAngleInv q).1) q : ℝ) : ℂ) * D [0] (actionAngleInv q) +
  ((coordPartial j (fun q ↦ (actionAngleInv q).2) q : ℝ) : ℂ) * D [1] (actionAngleInv q)

private theorem phase_smooth (lam : ℝ) : ContDiffOn ℝ ∞ (phase lam) actionStrip := by
  have hS : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ orbitPeriod q.1) actionStrip :=
    contDiffOn_orbitPeriod.comp contDiff_fst.contDiffOn (fun _ hq ↦ hq.1)
  exact (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_const.mul (contDiffOn_snd.mul hS)))).cexp

private theorem weight_smooth (lam : ℝ) : ContDiffOn ℝ ∞ (weight lam) actionStrip :=
  (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_orbitPeriod.comp contDiff_fst.contDiffOn (fun _ hq ↦ hq.1))).mul (phase_smooth lam)

private theorem fluxWeight_smooth (lam : ℝ) : ContDiffOn ℝ ∞ (fluxWeight lam) actionStrip :=
  (Complex.ofRealCLM.contDiff.comp_contDiffOn contDiffOn_snd).mul (phase_smooth lam)

private theorem weight_flux_identity (lam : ℝ) {q : ℝ × ℝ} (hq : q ∈ actionStrip) :
    coordPartial 0 (weight lam) q =
      ((deriv orbitPeriod q.1 : ℝ) : ℂ) * coordPartial 1 (fluxWeight lam) q := by
  have hS := ((contDiffOn_orbitPeriod.contDiffAt (Ioo_mem_nhds hq.1.1 hq.1.2)).differentiableAt
    (by simp)).hasDerivAt
  have hph := (((hS.const_mul q.2).const_mul lam).ofReal_comp.const_mul (-Complex.I)).cexp
  have hat := (((hasDerivAt_id q.2).mul_const (orbitPeriod q.1)).const_mul lam).ofReal_comp
  have hpt := (hat.const_mul (-Complex.I)).cexp
  have hw := (hS.ofReal_comp.mul hph).deriv
  have hp := ((hasDerivAt_id q.2).ofReal_comp.mul hpt).deriv
  change deriv (fun h ↦ weight lam (h, q.2)) q.1 =
    ((deriv orbitPeriod q.1 : ℝ) : ℂ) * deriv (fun t ↦ fluxWeight lam (q.1, t)) q.2
  dsimp only [weight, fluxWeight, phase]
  change deriv (fun h ↦ (orbitPeriod h : ℂ) *
    Complex.exp (-Complex.I * ((lam * (q.2 * orbitPeriod h) : ℝ) : ℂ))) q.1 = _ at hw
  change deriv (fun t : ℝ ↦ (t : ℂ) *
    Complex.exp (-Complex.I * ((lam * (t * orbitPeriod q.1) : ℝ) : ℂ))) q.2 = _ at hp
  rw [hw, hp]
  simp only [id_eq, one_mul]
  push_cast
  ring

private theorem orbit_flux_identity (lam : ℝ) (D : List (Fin 2) → ℝ × ℝ → ℂ)
    {q : ℝ × ℝ} (hq : q ∈ actionStrip) :
    weight lam q * chartGradient D 0 q =
      weight lam q * quarterForcingLevelDerivative D (q.1, q.2 * orbitPeriod q.1) +
      ((deriv orbitPeriod q.1 : ℝ) : ℂ) * fluxWeight lam q * chartGradient D 1 q := by
  let A := fderiv ℝ (fun p : ℝ × ℝ ↦ dipoleOrbit p.1 p.2)
    (q.1, q.2 * orbitPeriod q.1)
  have hd := ((contDiffAt_orbitMap (t := q.2 * orbitPeriod q.1) hq.1).differentiableAt
    (by simp)).hasFDerivAt
  have hS := ((contDiffOn_orbitPeriod.contDiffAt (Ioo_mem_nhds hq.1.1 hq.1.2)).differentiableAt
    (by simp)).hasDerivAt
  have h0 := hd.comp_hasDerivAt q.1 ((hasDerivAt_id q.1).prodMk (hS.const_mul q.2))
  have h1 := hd.comp_hasDerivAt q.2
    ((hasDerivAt_const q.2 q.1).prodMk ((hasDerivAt_id q.2).mul_const (orbitPeriod q.1)))
  have hV := hd.comp_hasDerivAt q.1
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 (q.2 * orbitPeriod q.1)))
  have hc0 : (coordPartial 0 (fun p ↦ (actionAngleInv p).1) q,
      coordPartial 0 (fun p ↦ (actionAngleInv p).2) q) =
      A (1, q.2 * deriv orbitPeriod q.1) := by
    ext
    · exact ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.1 h0).deriv
    · exact ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.1 h0).deriv
  have hc1 : (coordPartial 1 (fun p ↦ (actionAngleInv p).1) q,
      coordPartial 1 (fun p ↦ (actionAngleInv p).2) q) = A (0, orbitPeriod q.1) := by
    ext
    · simpa [coordPartial, partialY, actionAngleInv, A, Function.comp_def] using
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.2 h1).deriv
    · simpa [coordPartial, partialY, actionAngleInv, A, Function.comp_def] using
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.2 h1).deriv
  have hv : deriv (fun h ↦ dipoleOrbit h (q.2 * orbitPeriod q.1)) q.1 = A (1, 0) := hV.deriv
  have he : (orbitPeriod q.1) • A (1, q.2 * deriv orbitPeriod q.1) =
      (orbitPeriod q.1) • A (1, 0) + (q.2 * deriv orbitPeriod q.1) • A (0, orbitPeriod q.1) := by
    rw [← map_smul, ← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
    ring
  rw [← hc0, ← hc1, ← hv] at he
  have hx : (orbitPeriod q.1 : ℂ) *
      ((coordPartial 0 (fun p ↦ (actionAngleInv p).1) q : ℝ) : ℂ) =
      (orbitPeriod q.1 : ℂ) * ((deriv (fun h ↦ dipoleOrbit h (q.2 * orbitPeriod q.1)) q.1).1 : ℂ) +
      (q.2 : ℂ) * ((deriv orbitPeriod q.1 : ℝ) : ℂ) *
        ((coordPartial 1 (fun p ↦ (actionAngleInv p).1) q : ℝ) : ℂ) := by
    exact_mod_cast congrArg Prod.fst he
  have hy : (orbitPeriod q.1 : ℂ) *
      ((coordPartial 0 (fun p ↦ (actionAngleInv p).2) q : ℝ) : ℂ) =
      (orbitPeriod q.1 : ℂ) * ((deriv (fun h ↦ dipoleOrbit h (q.2 * orbitPeriod q.1)) q.1).2 : ℂ) +
      (q.2 : ℂ) * ((deriv orbitPeriod q.1 : ℝ) : ℂ) *
        ((coordPartial 1 (fun p ↦ (actionAngleInv p).2) q : ℝ) : ℂ) := by
    exact_mod_cast congrArg Prod.snd he
  dsimp only [weight, fluxWeight, chartGradient, quarterForcingLevelDerivative]
  dsimp only [actionAngleInv] at hx hy ⊢
  linear_combination phase lam q * D [0] (dipoleOrbit q.1 (q.2 * orbitPeriod q.1)) * hx +
    phase lam q * D [1] (dipoleOrbit q.1 (q.2 * orbitPeriod q.1)) * hy

/-- Normalization of any quarter-time integral, including a specified weak derivative. -/
theorem quarterIntervalIntegral_eq_normalized (h : ℝ) (F : ℝ → ℂ) :
    (∫ t in (-eighthPeriod h)..eighthPeriod h, F t) =
      ∫ θ in Icc (-1 / 8 : ℝ) (1 / 8), (orbitPeriod h : ℂ) * F (θ * orbitPeriod h) := by
  have he := intervalIntegral.smul_integral_comp_mul_right F
    (a := (-1 / 8 : ℝ)) (b := 1 / 8) (orbitPeriod h)
  have hm : (-1 / 8 : ℝ) * orbitPeriod h = -eighthPeriod h := by unfold orbitPeriod; ring
  have hp : (1 / 8 : ℝ) * orbitPeriod h = eighthPeriod h := by unfold orbitPeriod; ring
  rw [hm, hp] at he
  rw [← he, Complex.real_smul, ← intervalIntegral.integral_const_mul,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num :
      (-1 / 8 : ℝ) ≤ 1 / 8)]

private theorem endpoint_flux_eq (lam : ℝ) (g : ℝ × ℝ → ℂ) {h : ℝ}
    (hh : h ∈ Ioo (0 : ℝ) 1) :
    ((deriv orbitPeriod h : ℝ) : ℂ) *
      (fluxWeight lam (h, 1 / 8) * g (actionAngleInv (h, 1 / 8)) -
       fluxWeight lam (h, -1 / 8) * g (actionAngleInv (h, -1 / 8))) =
    ((deriv eighthPeriod h : ℝ) : ℂ) *
      (g (dipoleOrbit h (eighthPeriod h)) *
        Complex.exp (-Complex.I * ((lam * eighthPeriod h : ℝ) : ℂ)) +
       g (dipoleOrbit h (-eighthPeriod h)) *
        Complex.exp (-Complex.I * ((lam * (-eighthPeriod h) : ℝ) : ℂ))) := by
  have hL := ((contDiffOn_eighthPeriod.contDiffAt (Ioo_mem_nhds hh.1 hh.2)).differentiableAt
    (by simp)).hasDerivAt
  have hd : deriv orbitPeriod h = 8 * deriv eighthPeriod h := (hL.const_mul 8).deriv
  have hm : (-1 / 8 : ℝ) * orbitPeriod h = -eighthPeriod h := by unfold orbitPeriod; ring
  have hp : (1 / 8 : ℝ) * orbitPeriod h = eighthPeriod h := by unfold orbitPeriod; ring
  dsimp only [fluxWeight, phase, actionAngleInv]
  rw [hm, hp, hd]
  push_cast
  ring

/-- A fixed angular subwindow has the same weak level derivative and angular
boundary flux. The continuous forcing is evaluated only at the window ends. -/
theorem normalizedOrbitWindow_hasIntervalH1_flux {lam : ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) {g : ℝ × ℝ → ℂ} (hg : ContinuousOn g U)
    (hgL : MemLp g 2 (volume.restrict U))
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ j, HasWeakPartialOn U j g (D [j]))
    (hDL : ∀ j, MemLp (D [j]) 2 (volume.restrict U)) (hcell : cellSquare ⊆ U)
    {a b h₀ l r : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < h₀) (hh₀ : h₀ < 1)
    (hl : -1 / 4 < l) (hlr : l ≤ r) (hr : r < 3 / 4) :
    HasIntervalH1 a b
      (fun h ↦ ∫ θ in Icc l r, (orbitPeriod h : ℂ) *
        Complex.exp (-Complex.I * ((lam * (θ * orbitPeriod h) : ℝ) : ℂ)) *
          g (actionAngleInv (h, θ)))
      (fun h ↦ (∫ θ in Icc l r, (orbitPeriod h : ℂ) *
        Complex.exp (-Complex.I * ((lam * (θ * orbitPeriod h) : ℝ) : ℂ)) *
          quarterForcingLevelDerivative D (h, θ * orbitPeriod h)) +
        ((deriv orbitPeriod h : ℝ) : ℂ) *
          ((r : ℂ) * Complex.exp (-Complex.I * ((lam * (r * orbitPeriod h) : ℝ) : ℂ)) *
              g (actionAngleInv (h, r)) -
           (l : ℂ) * Complex.exp (-Complex.I * ((lam * (l * orbitPeriod h) : ℝ) : ℂ)) *
              g (actionAngleInv (h, l)))) := by
  let K : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (-1 / 4 : ℝ) (3 / 4)
  let R : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo (-1 / 4 : ℝ) (3 / 4)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hRo : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hRK : R ⊆ K := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hKs : K ⊆ actionStrip := fun q hq ↦
    ⟨⟨ha.trans_le hq.1.1, hq.1.2.trans_lt (hb.trans hh₀)⟩, mem_univ _⟩
  have hRs : R ⊆ actionStrip := hRK.trans hKs
  have hA : orbitAnnulus 0 h₀ ⊆ U := fun _ hp ↦ hcell hp.1.1
  have hP (u : ℝ × ℝ → ℂ) (hu : MemLp u 2 (volume.restrict U)) :
      MemLp (u ∘ actionAngleInv) 2 (volume.restrict R) :=
    memLp_actionAngleInv_band hU hu ha hab hb hh₀ hA
  have hM (C F : ℝ × ℝ → ℂ) (hC : ContDiffOn ℝ ∞ C actionStrip)
      (hF : MemLp F 2 (volume.restrict R)) :
      MemLp (fun q ↦ C q * F q) 2 (volume.restrict R) :=
    memLp_mul_on_compact hK hRo.measurableSet hRK (hC.continuousOn.mono hKs) hF
  have hG (j : Fin 2) : HasWeakPartialOn R j (g ∘ actionAngleInv) (chartGradient D j) :=
    (HasWeakPartialOn.comp_actionAngleInv (fun i ↦ (hD i).mono
      (sdiff_subset.trans hcell)) j).mono hRs
  have hGL (j : Fin 2) : MemLp (chartGradient D j) 2 (volume.restrict R) := by
    have hX := contDiffOn_coordPartial (isOpen_Ioo.prod isOpen_univ)
      (contDiff_fst.comp_contDiffOn contDiffOn_actionAngleInv) j
    have hY := contDiffOn_coordPartial (isOpen_Ioo.prod isOpen_univ)
      (contDiff_snd.comp_contDiffOn contDiffOn_actionAngleInv) j
    exact (hM _ _ (Complex.ofRealCLM.contDiff.comp_contDiffOn hX) (hP _ (hDL 0))).add
      (hM _ _ (Complex.ofRealCLM.contDiff.comp_contDiffOn hY) (hP _ (hDL 1)))
  have hgc : ContinuousOn (g ∘ actionAngleInv) R := hg.comp
    (contDiffOn_actionAngleInv.continuousOn.mono hRs)
    (fun q hq ↦ hcell (actionAngleInv_mem_puncturedCell (hRs hq).1.1 (hRs hq).1.2 q.2).1)
  have hW := weight_smooth lam
  have hPW := fluxWeight_smooth lam
  have hWx := contDiffOn_coordPartial (isOpen_Ioo.prod isOpen_univ) hW (0 : Fin 2)
  have hPy := contDiffOn_coordPartial (isOpen_Ioo.prod isOpen_univ) hPW (1 : Fin 2)
  have hβ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ ((deriv orbitPeriod q.1 : ℝ) : ℂ))
      actionStrip := Complex.ofRealCLM.contDiff.comp_contDiffOn
        ((contDiffOn_orbitPeriod.deriv_of_isOpen isOpen_Ioo (by simp)).comp
          contDiff_fst.contDiffOn (fun _ hq ↦ hq.1))
  let A : ℝ × ℝ → ℂ := fun q ↦ coordPartial 0 (weight lam) q * (g ∘ actionAngleInv) q +
    weight lam q * chartGradient D 0 q
  let B : ℝ × ℝ → ℂ := fun q ↦ coordPartial 1 (fluxWeight lam) q * (g ∘ actionAngleInv) q +
    fluxWeight lam q * chartGradient D 1 q
  let H : ℝ × ℝ → ℂ := fun q ↦ weight lam q *
    quarterForcingLevelDerivative D (q.1, q.2 * orbitPeriod q.1)
  have hAL : MemLp A 2 (volume.restrict R) :=
    (hM _ _ hWx (hP _ hgL)).add (hM _ _ hW (hGL 0))
  have hBL : MemLp B 2 (volume.restrict R) :=
    (hM _ _ hPy (hP _ hgL)).add (hM _ _ hPW (hGL 1))
  have hHL : MemLp H 2 (volume.restrict R) := by
    apply ((hM _ _ hW (hGL 0)).sub (hM _ _ (hβ.mul hPW) (hGL 1))).ae_eq
    filter_upwards [ae_restrict_mem hRo.measurableSet] with q hq
    dsimp only [Pi.mul_apply, Pi.sub_apply, H]
    linear_combination orbit_flux_identity lam D (hRs hq)
  have hx := (hG 0).mul_contDiffOn hRo (hW.mono hRs)
  have ht := (hG 1).mul_contDiffOn hRo (hPW.mono hRs)
  have hN := hx.setIntegral_h1_flux hab (by norm_num) hl hlr hr
    ((hW.continuousOn.mono hRs).mul hgc) ((hPW.continuousOn.mono hRs).mul hgc)
    (hM _ _ hW (hP _ hgL)) hAL hHL (hM _ _ hPW (hP _ hgL)) hBL ht
    (β := fun h ↦ ((deriv orbitPeriod h : ℝ) : ℂ)) (by
      intro q hq
      dsimp only [A, B, H]
      rw [weight_flux_identity lam (hRs hq), orbit_flux_identity lam D (hRs hq)]
      ring)
  simpa only [Pi.mul_apply, weight, fluxWeight, phase, H, Function.comp_apply] using hN

/-- The actual continuous forcing numerator has the moving-endpoint derivative
on each compact level interval. Only its specified first weak gradient is used. -/
theorem quarterNumerator_hasIntervalH1_derivative {lam : ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) {g : ℝ × ℝ → ℂ} (hg : ContinuousOn g U)
    (hgL : MemLp g 2 (volume.restrict U))
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ j, HasWeakPartialOn U j g (D [j]))
    (hDL : ∀ j, MemLp (D [j]) 2 (volume.restrict U)) (hcell : cellSquare ⊆ U)
    {a b h₀ : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < h₀) (hh₀ : h₀ < 1) :
    HasIntervalH1 a b (quarterNumerator lam g) (quarterNumeratorDerivative lam g D) := by
  have hN := normalizedOrbitWindow_hasIntervalH1_flux (lam := lam) hU hg hgL hD hDL hcell
    ha hab hb hh₀ (l := (-1 / 8 : ℝ)) (r := 1 / 8)
    (by norm_num) (by norm_num) (by norm_num)
  let H : ℝ × ℝ → ℂ := fun q ↦ weight lam q *
    quarterForcingLevelDerivative D (q.1, q.2 * orbitPeriod q.1)
  change HasIntervalH1 a b
    (fun h ↦ ∫ θ in Icc (-1 / 8 : ℝ) (1 / 8),
      weight lam (h, θ) * (g ∘ actionAngleInv) (h, θ))
    (fun h ↦ (∫ θ in Icc (-1 / 8 : ℝ) (1 / 8), H (h, θ)) +
      ((deriv orbitPeriod h : ℝ) : ℂ) *
        (fluxWeight lam (h, 1 / 8) * g (actionAngleInv (h, 1 / 8)) -
         fluxWeight lam (h, -1 / 8) * g (actionAngleInv (h, -1 / 8)))) at hN
  have hNv := hN.congr_Ioo (G := quarterNumerator lam g) (by
    intro h hh
    rw [quarterNumerator_eq_normalized]
    rfl)
  apply hNv.congr_derivative
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
  have hH : (∫ θ in Icc (-1 / 8 : ℝ) (1 / 8), H (h, θ)) =
      ∫ t in (-eighthPeriod h)..eighthPeriod h,
        quarterForcingLevelDerivative D (h, t) *
          Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ)) := by
    rw [quarterIntervalIntegral_eq_normalized]
    apply setIntegral_congr_fun measurableSet_Icc
    intro θ _
    dsimp only [H, weight, phase]
    ring
  rw [hH, endpoint_flux_eq lam g ⟨ha.trans hh.1, hh.2.trans (hb.trans hh₀)⟩]
  rfl

/-- Compatible local H¹ data with the exact moving-endpoint derivative. -/
theorem quarterNumerator_derivative_h1Loc {lam : ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) {g : ℝ × ℝ → ℂ} (hg : ContinuousOn g U)
    (hgL : MemLp g 2 (volume.restrict U))
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ j, HasWeakPartialOn U j g (D [j]))
    (hDL : ∀ j, MemLp (D [j]) 2 (volume.restrict U)) (hcell : cellSquare ⊆ U)
    {h₀ : ℝ} (hh₀ : h₀ < 1) :
    HasIntervalH1Loc 0 h₀ (quarterNumerator lam g) (quarterNumeratorDerivative lam g D) :=
  fun _ _ ha hab hb ↦ quarterNumerator_hasIntervalH1_derivative hU hg hgL hD hDL hcell
    ha hab hb hh₀

end NoEmbeddedEigenvalues
