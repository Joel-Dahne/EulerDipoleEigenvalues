import NoEmbeddedEigenvalues.LocalJets

/-! # Restriction, linearity and uniqueness of specified weak jets -/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set
open scoped ContDiff

/-- Specified jets restrict without changing any representative. -/
theorem HasWeakJetOn.mono {n : ℕ} {U V : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℂ}
    {D : List (Fin 2) → ℝ × ℝ → ℂ} (h : HasWeakJetOn n U f D) (hVU : V ⊆ U) :
    HasWeakJetOn n V f D :=
  ⟨h.1, fun w hw j ↦ (h.2 w hw j).mono hVU⟩

/-- Addition of specified jets. -/
theorem HasWeakJetOn.add {n : ℕ} {U : Set (ℝ × ℝ)} {f g : ℝ × ℝ → ℂ}
    {D E : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn n U f D) (hE : HasWeakJetOn n U g E) :
    HasWeakJetOn n U (fun p ↦ f p + g p) (fun w p ↦ D w p + E w p) :=
  ⟨by simp only [hD.1, hE.1], fun w hw j ↦ (hD.2 w hw j).add (hE.2 w hw j)⟩

/-- Uniqueness of all entries of a specified jet, on an open set. -/
theorem HasWeakJetOn.ae_eq {n : ℕ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ × ℝ → ℂ} {D E : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn n U f D) (hE : HasWeakJetOn n U f E) :
    ∀ w, w.length ≤ n → ∀ᵐ p, p ∈ U → D w p = E w p := by
  intro w
  induction w with
  | nil => intro _; simp only [hD.1, hE.1]; exact Filter.Eventually.of_forall (by simp)
  | cons j w ih =>
    intro hw
    have hw' : w.length < n := by simpa using hw
    have hd := (hD.2 w hw' j).congr_ae_on hU.measurableSet
      (ih (by omega)) (Filter.Eventually.of_forall fun _ _ ↦ rfl)
    exact hd.ae_eq hU (hE.2 w hw' j)

/-- Radial integrability restricts to smaller domains. -/
theorem RadialJetLp.mono {k s : ℕ} {U V : Set (ℝ × ℝ)} {c : ℝ × ℝ}
    {D : List (Fin 2) → ℝ × ℝ → ℂ} (h : RadialJetLp k s U c D) (hVU : V ⊆ U) :
    RadialJetLp k s V c D :=
  fun w hw ↦ (h w hw).mono_measure (Measure.restrict_mono hVU le_rfl)

/-- Addition preserves a common radial weight. -/
theorem RadialJetLp.add {k s : ℕ} {U : Set (ℝ × ℝ)} {c : ℝ × ℝ}
    {D E : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : RadialJetLp k s U c D) (hE : RadialJetLp k s U c E) :
    RadialJetLp k s U c (fun w p ↦ D w p + E w p) := by
  intro w hw
  simp_rw [add_div]
  exact MemLp.add (f := fun p ↦ D w p / (localRadius c p ^ s : ℂ))
    (g := fun p ↦ E w p / (localRadius c p ^ s : ℂ)) (hD w hw) (hE w hw)

/-- A smooth function has its classical specified jet on any domain. -/
theorem classicalComplexJet_weak {f : ℝ × ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (U : Set (ℝ × ℝ)) :
    HasWeakJetOn n U f (fun w ↦ classicalComplexJet w f) := by
  have hs (w : List (Fin 2)) : ContDiff ℝ ∞ (classicalComplexJet w f) := by
    induction w with
    | nil => exact hf
    | cons j w ih => exact contDiff_coordPartial_top j ih
  exact ⟨rfl, fun w _ j ↦ hasWeakPartialOn_of_contDiff ((hs w).of_le (by simp)) U j⟩

end NoEmbeddedEigenvalues
