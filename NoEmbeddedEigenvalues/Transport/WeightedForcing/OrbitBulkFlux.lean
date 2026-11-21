module

public import NoEmbeddedEigenvalues.Transport.WeightedForcing.SecondNumeratorBulk
public import NoEmbeddedEigenvalues.Transport.WeightedGains.OrbitTraceDerivative

/-!
# Weak differentiation of the first fixed-time bulk

Blueprint: `lem:time-rescaling-level`, `def:first-bulk-endpoint-trace`,
`lem:first-bulk-moving-endpoints`.

The time rescaling identity is applied both to the orbit and to its first
level vector. This keeps every ordered Cartesian second entry in its supplied
position; no weak mixed derivatives are commuted. Boundary values of the rough
first bulk are canonical normalized-angle traces, not raw gradient-ray values.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- Differentiating after a level-dependent time rescaling separates fixed-time
level differentiation from the transverse flux. No division by the clock occurs. -/
theorem timeRescaling_level_identity {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : ℝ × ℝ → E} {S : ℝ → ℝ} {h θ s : ℝ}
    (hS : HasDerivAt S s h) (hF : DifferentiableAt ℝ F (h, θ * S h)) :
    S h • coordPartial 0 (fun q ↦ F (q.1, q.2 * S q.1)) (h, θ) =
      S h • coordPartial 0 F (h, θ * S h) +
        (θ * s) • coordPartial 1 (fun q ↦ F (q.1, q.2 * S q.1)) (h, θ) := by
  have h0 := hF.hasFDerivAt.comp_hasDerivAt h
    ((hasDerivAt_id h).prodMk (hS.const_mul θ))
  have h1 := hF.hasFDerivAt.comp_hasDerivAt θ
    ((hasDerivAt_const θ h).prodMk ((hasDerivAt_id θ).mul_const (S h)))
  have hv := hF.hasFDerivAt.comp_hasDerivAt h
    ((hasDerivAt_id h).prodMk (hasDerivAt_const h (θ * S h)))
  dsimp only [Function.comp_def, id_eq, one_mul] at h0 h1 hv
  change S h • deriv (fun x ↦ F (x, θ * S x)) h =
    S h • deriv (fun x ↦ F (x, θ * S h)) h +
      (θ * s) • deriv (fun t ↦ F (h, t * S h)) θ
  rw [h0.deriv, hv.deriv, h1.deriv, ← map_smul, ← map_smul, ← map_smul, ← map_add]
  congr 1
  ext <;> simp
  ring

private theorem partial_axis {F : ℝ × ℝ → ℝ × ℝ} {q : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F q) (i j : Fin 2) :
    coordPartial j (fun p ↦ axisCoord i (F p)) q = axisCoord i (coordPartial j F q) := by
  have h0 := hF.hasFDerivAt.comp_hasDerivAt q.1
    ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))
  have h1 := hF.hasFDerivAt.comp_hasDerivAt q.2
    ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
  fin_cases i <;> fin_cases j
  · change deriv (fun x ↦ (F (x, q.2)).1) q.1 = (deriv (fun x ↦ F (x, q.2)) q.1).1
    change HasDerivAt (fun x ↦ F (x, q.2)) _ q.1 at h0
    rw [h0.deriv]
    exact ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.1 h0).deriv
  · change deriv (fun t ↦ (F (q.1, t)).1) q.2 = (deriv (fun t ↦ F (q.1, t)) q.2).1
    change HasDerivAt (fun t ↦ F (q.1, t)) _ q.2 at h1
    rw [h1.deriv]
    exact ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.2 h1).deriv
  · change deriv (fun x ↦ (F (x, q.2)).2) q.1 = (deriv (fun x ↦ F (x, q.2)) q.1).2
    change HasDerivAt (fun x ↦ F (x, q.2)) _ q.1 at h0
    rw [h0.deriv]
    exact ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.1 h0).deriv
  · change deriv (fun t ↦ (F (q.1, t)).2) q.2 = (deriv (fun t ↦ F (q.1, t)) q.2).2
    change HasDerivAt (fun t ↦ F (q.1, t)) _ q.2 at h1
    rw [h1.deriv]
    exact ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.2 h1).deriv

private def clock (q : ℝ × ℝ) : ℝ × ℝ := (q.1, q.2 * orbitPeriod q.1)
private def V (q : ℝ × ℝ) : ℝ × ℝ := deriv (fun h ↦ dipoleOrbit h q.2) q.1
private def W (q : ℝ × ℝ) : ℝ × ℝ := deriv (fun h ↦ deriv (fun x ↦ dipoleOrbit x q.2) h) q.1
private def phase (lam : ℝ) (q : ℝ × ℝ) : ℂ :=
  Complex.exp (-Complex.I * ((lam * (q.2 * orbitPeriod q.1) : ℝ) : ℂ))
private def weight (lam : ℝ) (q : ℝ × ℝ) : ℂ := (orbitPeriod q.1 : ℂ) * phase lam q
private def fluxWeight (lam : ℝ) (q : ℝ × ℝ) : ℂ := (q.2 : ℂ) * phase lam q
private def C (i : Fin 2) (q : ℝ × ℝ) : ℂ := (axisCoord i (V (clock q)) : ℂ)

private theorem clock_smooth : ContDiffOn ℝ ∞ clock actionStrip :=
  contDiffOn_fst.prodMk (contDiffOn_snd.mul
    (contDiffOn_orbitPeriod.comp contDiffOn_fst (fun _ hq ↦ hq.1)))

private theorem C_smooth (i : Fin 2) : ContDiffOn ℝ ∞ (C i) actionStrip := by
  have hv : ContDiffOn ℝ ∞ (V ∘ clock) actionStrip := by
    intro q hq
    exact ((contDiffAt_orbit_level_derivative (t := (clock q).2) hq.1).comp q
      (clock_smooth.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq))).contDiffWithinAt
  fin_cases i
  · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiff_fst.comp_contDiffOn hv)
  · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiff_snd.comp_contDiffOn hv)

private theorem phase_smooth (lam : ℝ) : ContDiffOn ℝ ∞ (phase lam) actionStrip := by
  have hS : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ orbitPeriod q.1) actionStrip :=
    contDiffOn_orbitPeriod.comp contDiffOn_fst (fun _ hq ↦ hq.1)
  exact (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_const.mul (contDiffOn_snd.mul hS)))).cexp

private theorem weight_smooth (lam : ℝ) : ContDiffOn ℝ ∞ (weight lam) actionStrip :=
  (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_orbitPeriod.comp contDiffOn_fst (fun _ hq ↦ hq.1))).mul (phase_smooth lam)

private theorem fluxWeight_smooth (lam : ℝ) : ContDiffOn ℝ ∞ (fluxWeight lam) actionStrip :=
  (Complex.ofRealCLM.contDiff.comp_contDiffOn contDiffOn_snd).mul (phase_smooth lam)

private theorem C_frame (i : Fin 2) {q : ℝ × ℝ} (hq : q ∈ actionStrip) :
    (orbitPeriod q.1 : ℂ) * coordPartial 0 (C i) q =
      (orbitPeriod q.1 : ℂ) * (axisCoord i (W (clock q)) : ℂ) +
        (q.2 : ℂ) * ((deriv orbitPeriod q.1 : ℝ) : ℂ) * coordPartial 1 (C i) q := by
  have hS := ((contDiffOn_orbitPeriod.contDiffAt (Ioo_mem_nhds hq.1.1 hq.1.2)).differentiableAt
    (by simp)).hasDerivAt
  have hv := (contDiffAt_orbit_level_derivative (t := (clock q).2) hq.1).differentiableAt (by simp)
  have hvcomp : DifferentiableAt ℝ (V ∘ clock) q := by
    exact hv.comp q ((clock_smooth.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq)).differentiableAt (by simp))
  have he := timeRescaling_level_identity hS hv
  have hc (j : Fin 2) : coordPartial j (C i) q =
      (axisCoord i (coordPartial j (V ∘ clock) q) : ℂ) := by
    have hi : DifferentiableAt ℝ (fun p ↦ axisCoord i ((V ∘ clock) p)) q := by
      fin_cases i
      · exact hvcomp.fst
      · exact hvcomp.snd
    have hc : coordPartial j (C i) q =
        ((coordPartial j (fun p ↦ axisCoord i ((V ∘ clock) p)) q : ℝ) : ℂ) := by
      fin_cases j
      · exact (hasDerivAt_partialX hi).ofReal_comp.deriv
      · exact (hasDerivAt_partialY hi).ofReal_comp.deriv
    rw [hc, partial_axis hvcomp]
  rw [hc 0, hc 1]
  change (orbitPeriod q.1 : ℂ) * (axisCoord i (coordPartial 0 (V ∘ clock) q) : ℂ) =
    (orbitPeriod q.1 : ℂ) * (axisCoord i (coordPartial 0 V (clock q)) : ℂ) + _
  have he' : orbitPeriod q.1 • coordPartial 0 (V ∘ clock) q =
      orbitPeriod q.1 • coordPartial 0 V (clock q) +
        (q.2 * deriv orbitPeriod q.1) • coordPartial 1 (V ∘ clock) q := he
  have hr : orbitPeriod q.1 * axisCoord i (coordPartial 0 (V ∘ clock) q) =
      orbitPeriod q.1 * axisCoord i (coordPartial 0 V (clock q)) +
        (q.2 * deriv orbitPeriod q.1) * axisCoord i (coordPartial 1 (V ∘ clock) q) := by
    fin_cases i
    · simpa [axisCoord, smul_eq_mul] using congrArg Prod.fst he'
    · simpa [axisCoord, smul_eq_mul] using congrArg Prod.snd he'
  exact_mod_cast hr

private def Pcoeff (i j : Fin 2) (q : ℝ × ℝ) : ℂ :=
  ((coordPartial j (fun p ↦ axisCoord i (actionAngleInv p)) q : ℝ) : ℂ)

private theorem P_frame (i : Fin 2) {q : ℝ × ℝ} (hq : q ∈ actionStrip) :
    (orbitPeriod q.1 : ℂ) * Pcoeff i 0 q = (orbitPeriod q.1 : ℂ) * C i q +
      (q.2 : ℂ) * ((deriv orbitPeriod q.1 : ℝ) : ℂ) * Pcoeff i 1 q := by
  have hS := ((contDiffOn_orbitPeriod.contDiffAt (Ioo_mem_nhds hq.1.1 hq.1.2)).differentiableAt
    (by simp)).hasDerivAt
  have hd := (contDiffAt_orbitMap (t := (clock q).2) hq.1).differentiableAt (by simp)
  have hP := (contDiffOn_actionAngleInv.contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq)).differentiableAt (by simp)
  have he := timeRescaling_level_identity hS hd
  have he' : orbitPeriod q.1 • coordPartial 0 actionAngleInv q =
      orbitPeriod q.1 • V (clock q) +
        (q.2 * deriv orbitPeriod q.1) • coordPartial 1 actionAngleInv q := he
  have hr : orbitPeriod q.1 * axisCoord i (coordPartial 0 actionAngleInv q) =
      orbitPeriod q.1 * axisCoord i (V (clock q)) +
        (q.2 * deriv orbitPeriod q.1) * axisCoord i (coordPartial 1 actionAngleInv q) := by
    fin_cases i
    · simpa [axisCoord, smul_eq_mul] using congrArg Prod.fst he'
    · simpa [axisCoord, smul_eq_mul] using congrArg Prod.snd he'
  dsimp only [Pcoeff, C]
  rw [partial_axis hP i 0, partial_axis hP i 1]
  exact_mod_cast hr

private theorem weight_frame (lam : ℝ) {q : ℝ × ℝ} (hq : q ∈ actionStrip) :
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

private theorem second_expansion (D : List (Fin 2) → ℝ × ℝ → ℂ) (q : ℝ × ℝ) :
    quarterForcingSecondLevelDerivative D q =
      (W q).1 * D [0] (dipoleOrbit q.1 q.2) + (W q).2 * D [1] (dipoleOrbit q.1 q.2) +
      (V q).1 * (V q).1 * D [0, 0] (dipoleOrbit q.1 q.2) +
      (V q).1 * (V q).2 * D [0, 1] (dipoleOrbit q.1 q.2) +
      (V q).2 * (V q).1 * D [1, 0] (dipoleOrbit q.1 q.2) +
      (V q).2 * (V q).2 * D [1, 1] (dipoleOrbit q.1 q.2) := by
  have he (f : (Fin 2 → Fin 2) → ℂ) : (∑ w, f w) =
      ∑ x : Fin 2, ∑ y : Fin 2, f ![x, y] := by
    rw [← (finTwoArrowEquiv (Fin 2)).symm.sum_comp f, Fintype.sum_prod_type]
    rfl
  simp only [quarterForcingSecondLevelDerivative, he, Fin.sum_univ_two, List.ofFn_succ,
    List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_one, axisCoord]
  push_cast
  dsimp only [V, W]
  ring

private def rowPartial (D : List (Fin 2) → ℝ × ℝ → ℂ) (k j : Fin 2)
    (q : ℝ × ℝ) : ℂ :=
  Pcoeff 0 j q * D [0, k] (actionAngleInv q) +
    Pcoeff 1 j q * D [1, k] (actionAngleInv q)

private def firstN (D : List (Fin 2) → ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  C 0 q * D [0] (actionAngleInv q) + C 1 q * D [1] (actionAngleInv q)

private def bulkPartial (D : List (Fin 2) → ℝ × ℝ → ℂ) (j : Fin 2)
    (q : ℝ × ℝ) : ℂ :=
  (coordPartial j (C 0) q * D [0] (actionAngleInv q) + C 0 q * rowPartial D 0 j q) +
    (coordPartial j (C 1) q * D [1] (actionAngleInv q) + C 1 q * rowPartial D 1 j q)

private theorem Pcoeff_smooth (i j : Fin 2) : ContDiffOn ℝ ∞ (Pcoeff i j) actionStrip := by
  have hi : ContDiffOn ℝ ∞ (fun q ↦ axisCoord i (actionAngleInv q)) actionStrip := by
    fin_cases i
    · exact contDiff_fst.comp_contDiffOn contDiffOn_actionAngleInv
    · exact contDiff_snd.comp_contDiffOn contDiffOn_actionAngleInv
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_coordPartial (isOpen_Ioo.prod isOpen_univ) hi j)

private theorem bulk_frame (lam : ℝ) (D : List (Fin 2) → ℝ × ℝ → ℂ)
    {q : ℝ × ℝ} (hq : q ∈ actionStrip) :
    weight lam q * bulkPartial D 0 q =
      weight lam q * quarterForcingSecondLevelDerivative D (clock q) +
        ((deriv orbitPeriod q.1 : ℝ) : ℂ) * fluxWeight lam q * bulkPartial D 1 q := by
  have hx := P_frame 0 hq
  have hy := P_frame 1 hq
  have hVx := C_frame 0 hq
  have hVy := C_frame 1 hq
  simp only [axisCoord, Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte] at hVx hVy
  have hs : quarterForcingSecondLevelDerivative D (clock q) =
      (W (clock q)).1 * D [0] (actionAngleInv q) +
      (W (clock q)).2 * D [1] (actionAngleInv q) +
      C 0 q * C 0 q * D [0, 0] (actionAngleInv q) +
      C 0 q * C 1 q * D [0, 1] (actionAngleInv q) +
      C 1 q * C 0 q * D [1, 0] (actionAngleInv q) +
      C 1 q * C 1 q * D [1, 1] (actionAngleInv q) := second_expansion D (clock q)
  rw [hs]
  dsimp only [bulkPartial, rowPartial, weight, fluxWeight]
  linear_combination phase lam q * D [0] (actionAngleInv q) * hVx +
    phase lam q * D [1] (actionAngleInv q) * hVy +
    phase lam q * C 0 q * D [0, 0] (actionAngleInv q) * hx +
    phase lam q * C 0 q * D [1, 0] (actionAngleInv q) * hy +
    phase lam q * C 1 q * D [0, 1] (actionAngleInv q) * hx +
    phase lam q * C 1 q * D [1, 1] (actionAngleInv q) * hy

/-- Canonical normalized boundary potential for the rough first fixed-time
bulk. The factor θ and oscillatory phase belong inside the section germ. -/
def quarterFirstBulkTrace (lam : ℝ) (D : List (Fin 2) → ℝ × ℝ → ℂ)
    (θ h : ℝ) : ℂ :=
  interiorSectionTrace (fun s ↦ ((θ + s : ℝ) : ℂ) *
    Complex.exp (-Complex.I * ((lam * ((θ + s) * orbitPeriod h) : ℝ) : ℂ)) *
      quarterForcingLevelDerivative D (h, (θ + s) * orbitPeriod h))

/-- The actual raw first fixed-time bulk has an H¹ representative, whose weak
derivative is the existing second fixed-time bulk plus canonical endpoint flux.
Only the indicated ordered rows are used; neither the forcing nor its gradient
is assumed continuous. -/
theorem quarterFirstBulk_hasIntervalH1_rep {lam : ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hcell : cellSquare ⊆ U)
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ i j, HasWeakPartialOn U i (D [j]) (D [i, j]))
    (hDL : ∀ j, MemLp (D [j]) 2 (volume.restrict U))
    (hD₂L : ∀ i j, MemLp (D [i, j]) 2 (volume.restrict U))
    {a b h₀ : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < h₀) (hh₀ : h₀ < 1) :
    ∃ A : ℝ → ℂ, A =ᵐ[volume.restrict (Ioo a b)]
        (fun h ↦ ∫ t in (-eighthPeriod h)..eighthPeriod h,
          quarterForcingLevelDerivative D (h, t) *
            Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))) ∧
      HasIntervalH1 a b A (fun h ↦ quarterSecondBulk lam D h +
        ((deriv orbitPeriod h : ℝ) : ℂ) *
          (quarterFirstBulkTrace lam D (1 / 8) h - quarterFirstBulkTrace lam D (-1 / 8) h)) := by
  let K : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (-1 / 4 : ℝ) (3 / 4)
  let R : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo (-1 / 4 : ℝ) (3 / 4)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hRo : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hSo : IsOpen actionStrip := isOpen_Ioo.prod isOpen_univ
  have hRK : R ⊆ K := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hKs : K ⊆ actionStrip := fun q hq ↦
    ⟨⟨ha.trans_le hq.1.1, hq.1.2.trans_lt (hb.trans hh₀)⟩, mem_univ _⟩
  have hRs : R ⊆ actionStrip := hRK.trans hKs
  have hP (u : ℝ × ℝ → ℂ) (hu : MemLp u 2 (volume.restrict U)) :
      MemLp (u ∘ actionAngleInv) 2 (volume.restrict R) :=
    memLp_actionAngleInv_band hU hu ha hab hb hh₀ (fun p hp ↦ hcell hp.1.1)
  have hM (c F : ℝ × ℝ → ℂ) (hc : ContDiffOn ℝ ∞ c actionStrip)
      (hF : MemLp F 2 (volume.restrict R)) :
      MemLp (fun q ↦ c q * F q) 2 (volume.restrict R) :=
    memLp_mul_on_compact hK hRo.measurableSet hRK (hc.continuousOn.mono hKs) hF
  have hG (k j : Fin 2) : HasWeakPartialOn R j (D [k] ∘ actionAngleInv) (rowPartial D k j) :=
    (HasWeakPartialOn.comp_actionAngleInv
      (fun i ↦ (hD i k).mono (sdiff_subset.trans hcell)) j).mono hRs
  have hGL (k j : Fin 2) : MemLp (rowPartial D k j) 2 (volume.restrict R) :=
    (hM _ _ (Pcoeff_smooth 0 j) (hP _ (hD₂L 0 k))).add
      (hM _ _ (Pcoeff_smooth 1 j) (hP _ (hD₂L 1 k)))
  have hGP (j : Fin 2) : HasWeakPartialOn R j (firstN D) (bulkPartial D j) :=
    ((hG 0 j).mul_contDiffOn hRo ((C_smooth 0).mono hRs)).add
      ((hG 1 j).mul_contDiffOn hRo ((C_smooth 1).mono hRs))
  have hFL : MemLp (firstN D) 2 (volume.restrict R) :=
    (hM _ _ (C_smooth 0) (hP _ (hDL 0))).add (hM _ _ (C_smooth 1) (hP _ (hDL 1)))
  have hPL (j : Fin 2) : MemLp (bulkPartial D j) 2 (volume.restrict R) :=
    ((hM _ _ (contDiffOn_coordPartial hSo (C_smooth 0) j) (hP _ (hDL 0))).add
      (hM _ _ (C_smooth 0) (hGL 0 j))).add
      ((hM _ _ (contDiffOn_coordPartial hSo (C_smooth 1) j) (hP _ (hDL 1))).add
        (hM _ _ (C_smooth 1) (hGL 1 j)))
  let A : ℝ × ℝ → ℂ := fun q ↦ coordPartial 0 (weight lam) q * firstN D q +
    weight lam q * bulkPartial D 0 q
  let B : ℝ × ℝ → ℂ := fun q ↦ coordPartial 1 (fluxWeight lam) q * firstN D q +
    fluxWeight lam q * bulkPartial D 1 q
  let H : ℝ × ℝ → ℂ := fun q ↦ weight lam q * quarterForcingSecondLevelDerivative D (clock q)
  have hAL : MemLp A 2 (volume.restrict R) :=
    (hM _ _ (contDiffOn_coordPartial hSo (weight_smooth lam) 0) hFL).add
      (hM _ _ (weight_smooth lam) (hPL 0))
  have hBL : MemLp B 2 (volume.restrict R) :=
    (hM _ _ (contDiffOn_coordPartial hSo (fluxWeight_smooth lam) 1) hFL).add
      (hM _ _ (fluxWeight_smooth lam) (hPL 1))
  have hβ : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ ((deriv orbitPeriod q.1 : ℝ) : ℂ))
      actionStrip := Complex.ofRealCLM.contDiff.comp_contDiffOn
        ((contDiffOn_orbitPeriod.deriv_of_isOpen isOpen_Ioo (by simp)).comp
          contDiffOn_fst (fun _ hq ↦ hq.1))
  have he (q : ℝ × ℝ) (hq : q ∈ R) :
      A q = H q + ((deriv orbitPeriod q.1 : ℝ) : ℂ) * B q := by
    dsimp only [A, B, H]
    rw [weight_frame lam (hRs hq), bulk_frame lam D (hRs hq)]
    ring
  have hHL : MemLp H 2 (volume.restrict R) := by
    apply (hAL.sub (hM _ _ hβ hBL)).ae_eq
    filter_upwards [ae_restrict_mem hRo.measurableSet] with q hq
    dsimp only [Pi.sub_apply]
    linear_combination he q hq
  have hx := (hGP 0).mul_contDiffOn hRo ((weight_smooth lam).mono hRs)
  obtain ⟨Z, hZe, hZ⟩ := hx.exists_setIntegral_h1_flux_rep hab (by norm_num)
      (l := (-1 / 8 : ℝ)) (r := 1 / 8)
      (by norm_num) (by norm_num) (by norm_num)
      (hM _ _ (weight_smooth lam) hFL) hAL hHL
      (hM _ _ (fluxWeight_smooth lam) hFL) hBL
      ((hGP 1).mul_contDiffOn hRo ((fluxWeight_smooth lam).mono hRs))
      (β := fun h ↦ ((deriv orbitPeriod h : ℝ) : ℂ))
      (by filter_upwards [ae_restrict_mem hRo.measurableSet] with q hq; exact he q hq)
  have hfirst (h : ℝ) :
      (∫ θ in Icc (-1 / 8 : ℝ) (1 / 8), weight lam (h, θ) * firstN D (h, θ)) =
        ∫ t in (-eighthPeriod h)..eighthPeriod h,
          quarterForcingLevelDerivative D (h, t) *
            Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ)) := by
    rw [quarterIntervalIntegral_eq_normalized]
    apply setIntegral_congr_fun measurableSet_Icc
    intro θ _
    dsimp only [weight, phase, firstN, C, V, clock, axisCoord, quarterForcingLevelDerivative,
      actionAngleInv]
    simp only [Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
    ring
  have hsecond (h : ℝ) : (∫ θ in Icc (-1 / 8 : ℝ) (1 / 8), H (h, θ)) =
      quarterSecondBulk lam D h := by
    rw [quarterSecondBulk, quarterIntervalIntegral_eq_normalized]
    apply setIntegral_congr_fun measurableSet_Icc
    intro θ _
    dsimp only [H, weight, phase, clock]
    ring
  refine ⟨Z, hZe.trans (Eventually.of_forall hfirst), ?_⟩
  simpa only [hsecond, quarterFirstBulkTrace, fluxWeight, phase, firstN, C, V, clock,
    axisCoord, Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
    quarterForcingLevelDerivative, actionAngleInv] using hZ

/-- Retain a supplied continuous representative of the raw first bulk. This is
used with the ordinary numerator derivative minus its continuous endpoint flux. -/
theorem quarterFirstBulk_hasIntervalH1_of_ae_eq {lam : ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hcell : cellSquare ⊆ U)
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ i j, HasWeakPartialOn U i (D [j]) (D [i, j]))
    (hDL : ∀ j, MemLp (D [j]) 2 (volume.restrict U))
    (hD₂L : ∀ i j, MemLp (D [i, j]) 2 (volume.restrict U))
    {a b h₀ : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < h₀) (hh₀ : h₀ < 1)
    {A : ℝ → ℂ} (hAc : ContinuousOn A (Ioo a b))
    (hAe : A =ᵐ[volume.restrict (Ioo a b)]
      (fun h ↦ ∫ t in (-eighthPeriod h)..eighthPeriod h,
        quarterForcingLevelDerivative D (h, t) *
          Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ)))) :
    HasIntervalH1 a b A (fun h ↦ quarterSecondBulk lam D h +
      ((deriv orbitPeriod h : ℝ) : ℂ) *
        (quarterFirstBulkTrace lam D (1 / 8) h - quarterFirstBulkTrace lam D (-1 / 8) h)) := by
  obtain ⟨B, hBe, hB⟩ := quarterFirstBulk_hasIntervalH1_rep hU hcell hD hDL hD₂L ha hab hb hh₀
  exact hB.congr_Ioo (Measure.eqOn_open_of_ae_eq (hBe.trans hAe.symm) isOpen_Ioo
    (hB.continuousOn_Ioo hab) hAc)

end NoEmbeddedEigenvalues
