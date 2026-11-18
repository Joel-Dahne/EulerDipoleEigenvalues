import NoEmbeddedEigenvalues.WeakChartTransportVariable
import NoEmbeddedEigenvalues.QuarterGradient
import NoEmbeddedEigenvalues.SecondNumeratorBulk

/-!
# The specified Cartesian gradient in fixed-time quarter coordinates

Blueprint: `def:quarter-forward-gradient`, `lem:quarter-forward-weak`,
`lem:quarter-raw-congruence`.

The forward chart has determinant two. Its inverse cofactors are the forward
coordinate vectors divided by two; the same factor cancels in the weak chain
rule. All entries are the supplied raw representatives.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

private theorem det_plane_entries (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) :
    A.det = (A (1, 0)).1 * (A (0, 1)).2 - (A (0, 1)).1 * (A (1, 0)).2 := by
  change LinearMap.det (A : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) = _
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Module.Basis.finTwoProd_zero,
    Module.Basis.finTwoProd_one, Module.Basis.coe_finTwoProd_repr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    ContinuousLinearMap.coe_coe]

private theorem inverse_plane_entries (A B : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (hAB : A.comp B = ContinuousLinearMap.id ℝ (ℝ × ℝ)) (hdet : A.det = 2) :
    B.det = 1 / 2 ∧ (B (1, 0)).1 = (A (0, 1)).2 / 2 ∧
      (B (1, 0)).2 = -(A (1, 0)).2 / 2 ∧
      (B (0, 1)).1 = -(A (0, 1)).1 / 2 ∧
      (B (0, 1)).2 = (A (1, 0)).1 / 2 := by
  have ha := (det_plane_entries A).symm.trans hdet
  have hA (u : ℝ × ℝ) : A u = u.1 • A (1, 0) + u.2 • A (0, 1) := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  have hv (v : ℝ × ℝ) := congrArg (fun L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) ↦ L v) hAB
  have he (v : ℝ × ℝ) :
      2 * (B v).1 = (A (0, 1)).2 * v.1 - (A (0, 1)).1 * v.2 ∧
      2 * (B v).2 = (A (1, 0)).1 * v.2 - (A (1, 0)).2 * v.1 := by
    have hv' : A (B v) = v := hv v
    rw [hA] at hv'
    have hx := congrArg Prod.fst hv'
    have hy := congrArg Prod.snd hv'
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hx hy
    constructor
    · linear_combination (A (0, 1)).2 * hx - (A (0, 1)).1 * hy - (B v).1 * ha
    · linear_combination (A (1, 0)).1 * hy - (A (1, 0)).2 * hx - (B v).2 * ha
  have h00 : (B (1, 0)).1 = (A (0, 1)).2 / 2 := by linarith [(he (1, 0)).1]
  have h10 : (B (1, 0)).2 = -(A (1, 0)).2 / 2 := by linarith [(he (1, 0)).2]
  have h01 : (B (0, 1)).1 = -(A (0, 1)).1 / 2 := by linarith [(he (0, 1)).1]
  have h11 : (B (0, 1)).2 = (A (1, 0)).1 / 2 := by linarith [(he (0, 1)).2]
  refine ⟨?_, h00, h10, h01, h11⟩
  rw [det_plane_entries, h00, h10, h01, h11]
  nlinarith only [ha]

/-- The two fixed-time forward coordinate vectors. -/
def quarterForwardVector (j : Fin 2) (q : ℝ × ℝ) : ℝ × ℝ :=
  if j = 0 then deriv (fun h ↦ dipoleOrbit h q.2) q.1
  else dipoleVelocity (dipoleOrbit q.1 q.2)

/-- The forward contraction keeps the original Cartesian entries. -/
def quarterPullbackDerivative (D : Fin 2 → ℝ × ℝ → ℂ) (j : Fin 2) (q : ℝ × ℝ) : ℂ :=
  ((quarterForwardVector j q).1 : ℂ) * D 0 (dipoleOrbit q.1 q.2) +
    ((quarterForwardVector j q).2 : ℂ) * D 1 (dipoleOrbit q.1 q.2)

private theorem forward_axis {b : ℝ} (hb : b ≤ 1) {q : ℝ × ℝ}
    (hq : q ∈ quarterOrbitStrip b) (j : Fin 2) :
    fderiv ℝ (quarterChart hb) q (if j = 0 then (1, 0) else (0, 1)) =
      quarterForwardVector j q := by
  have hd := ((contDiffOn_quarterChart hb).contDiffAt
    ((isOpen_quarterOrbitStrip hb).mem_nhds hq)).differentiableAt (by simp)
  fin_cases j
  · have hx := hd.hasFDerivAt.comp_hasDerivAt q.1
      ((hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2))
    exact hx.deriv.symm
  · have ht := hd.hasFDerivAt.comp_hasDerivAt q.2
      ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
    change HasDerivAt (fun t ↦ dipoleOrbit q.1 t)
      (fderiv ℝ (quarterChart hb) q (0, 1)) q.2 at ht
    change fderiv ℝ (quarterChart hb) q (0, 1) = dipoleVelocity (dipoleOrbit q.1 q.2)
    exact ht.unique (hasDerivAt_dipoleFlow (Real.arccos q.1, -Real.arccos q.1) q.2)

private theorem inverse_chart_frame {b : ℝ} (hb : b ≤ 1) {p : ℝ × ℝ}
    (hp : p ∈ quarterImage b) :
    (fderiv ℝ (quarterChart hb).symm p).det = 1 / 2 ∧
    ∀ j : Fin 2,
      chartCofactor (quarterChart hb).symm j 0 p =
        ((quarterForwardVector j ((quarterChart hb).symm p)).1 : ℂ) / 2 ∧
      chartCofactor (quarterChart hb).symm j 1 p =
        ((quarterForwardVector j ((quarterChart hb).symm p)).2 : ℂ) / 2 := by
  let e := quarterChart hb
  let q := e.symm p
  have hq : q ∈ quarterOrbitStrip b := hp.2
  have he : ContDiffOn ℝ ∞ e.symm (quarterImage b) := contDiffOn_quarterCoordinates
  have hdA := ((contDiffOn_quarterChart hb).contDiffAt
    ((isOpen_quarterOrbitStrip hb).mem_nhds hq)).differentiableAt (by simp)
  have hdB := (he.contDiffAt ((isOpen_quarterImage hb).mem_nhds hp)).differentiableAt (by simp)
  let A := fderiv ℝ e q
  let B := fderiv ℝ e.symm p
  have hAB : A.comp B = ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    have hd := (hdA.hasFDerivAt.comp p hdB.hasFDerivAt).fderiv
    change fderiv ℝ (fun p ↦ e (e.symm p)) p = A.comp B at hd
    have hEq : (fun p ↦ e (e.symm p)) =ᶠ[𝓝 p] id := by
      filter_upwards [(isOpen_quarterImage hb).mem_nhds hp] with p hp
      exact e.right_inv hp
    rw [hEq.fderiv_eq, fderiv_id] at hd
    exact hd.symm
  obtain ⟨hdet, h00, h10, h01, h11⟩ := inverse_plane_entries A B hAB
    (det_fderiv_quarterChart hb hq)
  refine ⟨hdet, ?_⟩
  intro j
  have hx := forward_axis hb hq (0 : Fin 2)
  have ht := forward_axis hb hq (1 : Fin 2)
  change A (1, 0) = quarterForwardVector 0 q at hx
  change A (0, 1) = quarterForwardVector 1 q at ht
  fin_cases j
  · change chartCofactor e.symm 0 0 p = ((quarterForwardVector 0 q).1 : ℂ) / 2 ∧
      chartCofactor e.symm 0 1 p = ((quarterForwardVector 0 q).2 : ℂ) / 2
    have hc := chartCofactor_values he (0 : Fin 2) hp
    simp only [↓reduceIte] at hc
    rw [hc.1, hc.2]
    change ((B (0, 1)).2 : ℂ) = _ ∧ -((B (1, 0)).2 : ℂ) = _
    rw [h11, h10, hx]
    push_cast
    constructor <;> ring
  · change chartCofactor e.symm 1 0 p = ((quarterForwardVector 1 q).1 : ℂ) / 2 ∧
      chartCofactor e.symm 1 1 p = ((quarterForwardVector 1 q).2 : ℂ) / 2
    have hc := chartCofactor_values he (1 : Fin 2) hp
    simp only [one_ne_zero, ↓reduceIte] at hc
    rw [hc.1, hc.2]
    change -((B (0, 1)).1 : ℂ) = _ ∧ ((B (1, 0)).1 : ℂ) = _
    rw [h01, h00, ht]
    push_cast
    constructor <;> ring

/-- Fixed-time weak chain rule for the supplied Cartesian gradient. -/
theorem HasWeakPartialOn.comp_quarterOrbit {b : ℝ} (hb : b ≤ 1)
    {U : Set (ℝ × ℝ)} {F : ℝ × ℝ → ℂ} {D : Fin 2 → ℝ × ℝ → ℂ}
    (hU : quarterImage b ⊆ U) (hD : ∀ j, HasWeakPartialOn U j F (D j))
    (hF : MemLp F 2 (volume.restrict cellSquare))
    (hDL : ∀ j, MemLp (D j) 2 (volume.restrict cellSquare)) (j : Fin 2) :
    HasWeakPartialOn (quarterOrbitStrip b) j (fun q ↦ F (dipoleOrbit q.1 q.2))
      (quarterPullbackDerivative D j) := by
  have hFp := memLp_comp_quarterOrbitStrip_of_memLp hb hF
  have hDp (i : Fin 2) := memLp_comp_quarterOrbitStrip_of_memLp hb (hDL i)
  have hloc (i : Fin 2) : LocallyIntegrableOn
      (fun q : ℝ × ℝ ↦ D i (dipoleOrbit q.1 q.2)) (quarterOrbitStrip b) :=
    locallyIntegrableOn_of_locallyIntegrable_restrict ((hDp i).locallyIntegrable (by norm_num))
  have hv : ContinuousOn (quarterForwardVector j) (quarterOrbitStrip b) := by
    unfold quarterForwardVector
    split_ifs
    · intro q hq
      exact (contDiffAt_orbit_level_derivative
        ⟨hq.1, hq.2.1.trans_le hb⟩).continuousAt.continuousWithinAt
    · have hX : Continuous dipoleVelocity := by unfold dipoleVelocity; fun_prop
      exact (hX.comp continuous_dipoleOrbit).continuousOn
  have hG : LocallyIntegrableOn (quarterPullbackDerivative D j) (quarterOrbitStrip b) :=
    ((hloc 0).continuousOn_mul (Complex.continuous_ofReal.comp_continuousOn hv.fst)
      (isOpen_quarterOrbitStrip hb).isLocallyClosed).add
    ((hloc 1).continuousOn_mul (Complex.continuous_ofReal.comp_continuousOn hv.snd)
      (isOpen_quarterOrbitStrip hb).isLocallyClosed)
  apply HasWeakPartialOn.of_comp_chart_pos
    (e := (quarterChart hb).symm) contDiffOn_quarterCoordinates
    (fun p hp ↦ by rw [(inverse_chart_frame hb hp).1]; norm_num)
    (fun i ↦ (hD i).mono hU)
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hFp.locallyIntegrable (by norm_num))) hG j
  · intro p hp
    change F (dipoleOrbit (levelCoord p) (timeCoord p)) = F p
    rw [dipoleOrbit_levelCoord_timeCoord hp.1.1]
  · intro p hp
    obtain ⟨hdet, hcof⟩ := inverse_chart_frame hb hp
    rw [hdet, (hcof j).1, (hcof j).2]
    have hinv := (quarterChart hb).right_inv hp
    change dipoleOrbit ((quarterChart hb).symm p).1 ((quarterChart hb).symm p).2 = p at hinv
    dsimp only [quarterPullbackDerivative]
    rw [hinv]
    push_cast
    ring

/-- Coarea transfers a spatial a.e. identity between raw L² representatives,
without assuming their chosen values are globally measurable. -/
theorem ae_eq_comp_quarterOrbitStrip_of_memLp {b : ℝ} (hb : b ≤ 1)
    {U : Set (ℝ × ℝ)} (hU : orbitAnnulus 0 b ⊆ U) {F G : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict cellSquare))
    (hG : MemLp G 2 (volume.restrict cellSquare)) (heq : F =ᵐ[volume.restrict U] G) :
    (fun q ↦ F (dipoleOrbit q.1 q.2)) =ᵐ[volume.restrict (quarterOrbitStrip b)]
      (fun q ↦ G (dipoleOrbit q.1 q.2)) := by
  apply ae_eq_quarterStrip_of_ae_sections
    (memLp_comp_quarterOrbitStrip_of_memLp hb hF).aestronglyMeasurable
    (memLp_comp_quarterOrbitStrip_of_memLp hb hG).aestronglyMeasurable
  have hsec := ae_orbit_congr hb (ae_restrict_of_ae_restrict_of_subset hU heq)
  exact hsec.mono fun _ hh ↦ ae_restrict_of_ae hh

end NoEmbeddedEigenvalues
