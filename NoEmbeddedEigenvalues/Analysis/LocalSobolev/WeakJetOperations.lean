module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.LocalJets

/-! # Restriction, linearity and uniqueness of specified weak jets -/

@[expose] public section

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

/-- Subtraction retains the specified representatives at every order. -/
theorem HasWeakJetOn.sub {n : ℕ} {U : Set (ℝ × ℝ)} {f g : ℝ × ℝ → ℂ}
    {D E : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn n U f D) (hE : HasWeakJetOn n U g E) :
    HasWeakJetOn n U (fun p ↦ f p - g p) (fun w p ↦ D w p - E w p) := by
  refine ⟨by simp only [hD.1, hE.1], fun w hw j ↦ ?_⟩
  simpa only [neg_one_mul, sub_eq_add_neg] using
    (hD.2 w hw j).add ((hE.2 w hw j).const_mul (-1))

/-- A.e. equality of the base functions identifies every specified weak entry. -/
theorem HasWeakJetOn.ae_eq_of_value_ae {n : ℕ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f g : ℝ × ℝ → ℂ} {D E : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn n U f D) (hE : HasWeakJetOn n U g E)
    (hfg : f =ᵐ[volume.restrict U] g) :
    ∀ w, w.length ≤ n → ∀ᵐ p, p ∈ U → D w p = E w p := by
  intro w
  induction w with
  | nil =>
    intro _
    simpa only [hD.1, hE.1] using (ae_restrict_iff' hU.measurableSet).mp hfg
  | cons j w ih =>
    intro hw
    have hw' : w.length < n := by simpa using hw
    have hd := (hD.2 w hw' j).congr_ae_on hU.measurableSet
      (ih (by omega)) (Filter.Eventually.of_forall fun _ _ ↦ rfl)
    exact hd.ae_eq hU (hE.2 w hw' j)

/-- Uniqueness of all entries of a specified jet, on an open set. -/
theorem HasWeakJetOn.ae_eq {n : ℕ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ × ℝ → ℂ} {D E : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn n U f D) (hE : HasWeakJetOn n U f E) :
    ∀ w, w.length ≤ n → ∀ᵐ p, p ∈ U → D w p = E w p :=
  hD.ae_eq_of_value_ae hU hE (Filter.Eventually.of_forall fun _ ↦ rfl)

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

/-- Recursive Sobolev regularity belongs to every specified weak partial, not
only to the witnesses used in its existential definition. -/
theorem HasWeakPartialOn.memSobolevOn {k : ℕ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {F D : ℝ × ℝ → ℂ} {j : Fin 2} (hd : HasWeakPartialOn U j F D)
    (hF : MemSobolevOn (k + 1) U F) : MemSobolevOn k U D := by
  obtain ⟨E, hE, hEk⟩ := hF.2 j
  exact MemSobolevOn.congr_ae_on hEk hU.measurableSet (hE.ae_eq hU hd)

/-- The specified derivative inherits local Sobolev regularity on the same domain. -/
theorem HasWeakPartialOn.memSobolevLocOn {k : ℕ} {U : Set (ℝ × ℝ)}
    {F D : ℝ × ℝ → ℂ} {j : Fin 2} (hd : HasWeakPartialOn U j F D)
    (hF : MemSobolevLocOn (k + 1) U F) : MemSobolevLocOn k U D := by
  intro V hV hVc hVU
  exact (hd.mono (subset_closure.trans hVU)).memSobolevOn hV (hF V hV hVc hVU)

/-- Regularity of every entry of a fixed weak jet. This does not replace the jet
by independently chosen representatives at successive differentiation steps. -/
theorem HasWeakJetOn.memSobolevLocOn {n m : ℕ} {U : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn n U F D) (hF : MemSobolevLocOn m U F)
    (w : List (Fin 2)) (hw : w.length ≤ n) (hm : w.length ≤ m) :
    MemSobolevLocOn (m - w.length) U (D w) := by
  induction w with
  | nil => simpa only [hD.1, List.length_nil, Nat.sub_zero] using hF
  | cons j w ih =>
    have hlen : w.length < n := by simp only [List.length_cons] at hw; omega
    have hi := ih (by omega) (by simp only [List.length_cons] at hm; omega)
    have he : m - w.length = (m - (j :: w).length) + 1 := by
      simp only [List.length_cons] at *
      omega
    rw [he] at hi
    exact (hD.2 w hlen j).memSobolevLocOn hi

end NoEmbeddedEigenvalues
