import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.LogPolarCoordinates

/-!
# Overlapping real-angle logarithmic-polar charts

Two angular cuts give an open cover of the punctured plane. Both chart maps
are the same actual logarithmic-polar parametrization on their entire source
coordinate plane; only their source windows and inverse branches differ.
This cover is for weak locality, not merely measure transport across a null cut.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open Set
open scoped ContDiff

/-- The real-angle chart with cut along the nonpositive horizontal axis. -/
def logPolarBaseChart : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) where
  toFun := logPolarPlane
  invFun p := (-Real.log (polarCoord p).1, (polarCoord p).2)
  source := logPolarStrip
  target := polarCoord.source
  map_source' q hq := by
    rw [← image_logPolarPlane_strip]
    exact mem_image_of_mem _ hq
  map_target' p hp := ⟨mem_univ _, (polarCoord.map_source hp).2⟩
  left_inv' q hq := by
    have h := polarCoord.right_inv (show (Real.exp (-q.1), q.2) ∈ polarCoord.target from
      ⟨Real.exp_pos _, hq.2⟩)
    change polarCoord (logPolarPlane q) = (Real.exp (-q.1), q.2) at h
    apply Prod.ext
    · change -Real.log (polarCoord (logPolarPlane q)).1 = q.1
      rw [congrArg Prod.fst h]
      simp
    · change (polarCoord (logPolarPlane q)).2 = q.2
      simpa only using congrArg Prod.snd h
  right_inv' p hp := by
    change polarCoord.symm
      (Real.exp (-(-Real.log (polarCoord p).1)), (polarCoord p).2) = p
    rw [neg_neg, Real.exp_log (polarCoord.map_source hp).1]
    exact polarCoord.left_inv hp
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := polarCoord.open_source
  continuousOn_toFun := continuous_logPolarPlane.continuousOn
  continuousOn_invFun :=
    ((polarCoord.continuousOn.fst.log (fun p hp ↦ (polarCoord.map_source hp).1.ne')).neg).prodMk
      polarCoord.continuousOn.snd

/-- The second chart uses angles between zero and two pi and the opposite cut. -/
def logPolarChart (opposite : Bool) : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
  if opposite then
    (((Homeomorph.addRight ((0, -Real.pi) : ℝ × ℝ)).toOpenPartialHomeomorph.trans
      logPolarBaseChart).trans (Homeomorph.neg (ℝ × ℝ)).toOpenPartialHomeomorph)
  else logPolarBaseChart

theorem logPolarChart_apply (b : Bool) (q : ℝ × ℝ) : logPolarChart b q = logPolarPlane q := by
  cases b
  · rfl
  · change -logPolarPlane (q + (0, -Real.pi)) = logPolarPlane q
    ext <;> simp [logPolarPlane, Real.cos_add, Real.sin_add]

theorem logPolarChart_target (b : Bool) : (logPolarChart b).target =
    if b then {p | -p ∈ polarCoord.source} else polarCoord.source := by
  cases b
  · rfl
  · ext p
    simp [logPolarChart, logPolarBaseChart]

@[fun_prop]
theorem contDiff_logPolarPlane : ContDiff ℝ ∞ logPolarPlane := by
  unfold logPolarPlane
  fun_prop

theorem contDiff_logPolarChart (b : Bool) : ContDiff ℝ ∞ (logPolarChart b) := by
  simpa only [show (logPolarChart b : (ℝ × ℝ) → ℝ × ℝ) = logPolarPlane from
    funext (logPolarChart_apply b)] using contDiff_logPolarPlane

theorem fderiv_logPolarChart (b : Bool) (q : ℝ × ℝ) :
    fderiv ℝ (logPolarChart b) q = logPolarDeriv q := by
  rw [show (logPolarChart b : (ℝ × ℝ) → ℝ × ℝ) = logPolarPlane from
    funext (logPolarChart_apply b)]
  exact (hasFDerivAt_logPolarPlane q).fderiv

theorem det_fderiv_logPolarChart (b : Bool) (q : ℝ × ℝ) :
    (fderiv ℝ (logPolarChart b) q).det = -(Real.exp (-q.1) ^ 2) := by
  rw [fderiv_logPolarChart, det_logPolarDeriv]

/-- Every nonzero point belongs to an actual open chart target. -/
theorem exists_logPolarChart_target {p : ℝ × ℝ} (hp : p ≠ 0) :
    ∃ b : Bool, p ∈ (logPolarChart b).target := by
  have hc : p ∈ polarCoord.source ∨ -p ∈ polarCoord.source := by
    change (0 < p.1 ∨ p.2 ≠ 0) ∨ (0 < -p.1 ∨ -p.2 ≠ 0)
    by_cases hy : p.2 = 0
    · have hx : p.1 ≠ 0 := fun hx ↦ hp (Prod.ext hx hy)
      rcases lt_or_gt_of_ne hx with hx | hx
      · exact Or.inr (Or.inl (neg_pos.mpr hx))
      · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hy)
  rcases hc with hc | hc
  · exact ⟨false, hc⟩
  · exact ⟨true, by simpa only [logPolarChart_target, ite_true, mem_ofPred_eq] using hc⟩

end NoEmbeddedEigenvalues
