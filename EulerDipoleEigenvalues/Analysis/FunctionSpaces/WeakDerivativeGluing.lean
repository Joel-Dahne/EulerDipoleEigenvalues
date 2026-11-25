module

public import EulerDipoleEigenvalues.Analysis.FunctionSpaces.WeakPartialLocality
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.SobolevGluing
public import Mathlib.Topology.Compactness.Lindelof

/-!
# Specified weak derivatives from local Sobolev regularity

Blueprint: `lem:local-h1-specified-gradient`.

Local H¹ witnesses need not use the same derivative representatives. A countable
subcover and weak uniqueness on overlaps glue their raw derivatives a.e.; weak
locality then gives one specified derivative on the whole open set.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

/-- Countably many compatible weak derivatives glue to one raw derivative.
The agreement on each patch is an a.e. assertion, not pointwise compatibility. -/
theorem exists_weakPartial_of_locally {U : Set (ℝ × ℝ)} {j : Fin 2}
    {F : ℝ × ℝ → ℂ}
    (hloc : ∀ p ∈ U, ∃ W : Set (ℝ × ℝ), IsOpen W ∧ p ∈ W ∧
      ∃ d : ℝ × ℝ → ℂ, HasWeakPartialOn W j F d ∧ MemSobolevLocOn 0 W d) :
    ∃ D : ℝ × ℝ → ℂ, HasWeakPartialOn U j F D ∧ MemSobolevLocOn 0 U D := by
  classical
  choose W hW hpW d hd hdl using fun p : U ↦ hloc p p.property
  obtain ⟨s, hs, hcover⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover
    W hW (fun p hp ↦ mem_iUnion_of_mem ⟨p, hp⟩ (hpW ⟨p, hp⟩))
  let : Countable s := hs.to_subtype
  let V (i : s) := W i.val
  let g (i : s) := d i.val
  let D (p : ℝ × ℝ) : ℂ :=
    if hp : ∃ i : s, p ∈ V i then g (Classical.choose hp) p else 0
  have hpatch (i : s) : ∀ᵐ p, p ∈ V i → g i p = D p := by
    have hpair (k : s) : ∀ᵐ p, p ∈ V i ∩ V k → g i p = g k p :=
      ((hd i.val).mono inter_subset_left).ae_eq ((hW i.val).inter (hW k.val))
        ((hd k.val).mono inter_subset_right)
    filter_upwards [ae_all_iff.2 hpair] with p hp hpV
    have hex : ∃ k : s, p ∈ V k := ⟨i, hpV⟩
    dsimp only [D]
    rw [dite_eq_left hex]
    exact hp (Classical.choose hex) ⟨hpV, Classical.choose_spec hex⟩
  have hpatchD (i : s) : HasWeakPartialOn (V i) j F D :=
    (hd i.val).congr_ae_on (hW i.val).measurableSet
      (Eventually.of_forall fun _ _ ↦ rfl) (hpatch i)
  have hpatchL (i : s) : MemSobolevLocOn 0 (V i) D :=
    (hdl i.val).congr_ae_on (hpatch i)
  have hlocal (p : ℝ × ℝ) (hp : p ∈ U) : ∃ i : s, p ∈ V i := by
    obtain ⟨i, his, hpi⟩ := mem_iUnion₂.mp (hcover hp)
    exact ⟨⟨i, his⟩, hpi⟩
  exact ⟨D, hasWeakPartialOn_of_locally (fun p hp ↦ by
      obtain ⟨i, hi⟩ := hlocal p hp
      exact ⟨V i, hW i.val, hi, hpatchD i⟩),
    memSobolevLocOn_of_locally (fun p hp ↦ by
      obtain ⟨i, hi⟩ := hlocal p hp
      exact ⟨V i, hW i.val, hi, hpatchL i⟩)⟩

/-- Local H¹ regularity on an open set supplies one specified weak gradient,
whose components have genuine local L² bounds on that same set. -/
theorem MemSobolevLocOn.exists_weakGradient {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {F : ℝ × ℝ → ℂ} (hF : MemSobolevLocOn 1 U F) :
    ∃ D : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
      HasWeakPartialOn U j F (D j) ∧ MemSobolevLocOn 0 U (D j) := by
  have hpartial (j : Fin 2) : ∃ D : ℝ × ℝ → ℂ,
      HasWeakPartialOn U j F D ∧ MemSobolevLocOn 0 U D := by
    apply exists_weakPartial_of_locally
    intro p hp
    obtain ⟨W, hW, hpW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure
      isCompact_singleton hU (singleton_subset_iff.2 hp)
    obtain ⟨d, hd, hdl⟩ := (hF W hW hWc hWU).2 j
    exact ⟨W, hW, hpW (mem_singleton p), d, hd,
      (show MemSobolevOn 0 W d from hdl).memSobolevLocOn⟩
  choose D hD using hpartial
  exact ⟨D, hD⟩

/-- The specified gradient can be chosen globally measurable, while all its
weak identities and local L² bounds remain on the original open set. -/
theorem MemSobolevLocOn.exists_measurable_weakGradient {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {F : ℝ × ℝ → ℂ} (hF : MemSobolevLocOn 1 U F) :
    ∃ D : Fin 2 → ℝ × ℝ → ℂ, ∀ j,
      Measurable (D j) ∧ HasWeakPartialOn U j F (D j) ∧ MemSobolevLocOn 0 U (D j) := by
  obtain ⟨g, hg⟩ := hF.exists_weakGradient hU
  have hm (j : Fin 2) := (hg j).1.2.1.aestronglyMeasurable
  let D (j : Fin 2) := (hm j).mk (g j)
  have he (j : Fin 2) : ∀ᵐ p, p ∈ U → g j p = D j p :=
    (ae_restrict_iff' hU.measurableSet).1 (hm j).ae_eq_mk
  refine ⟨D, fun j ↦ ⟨(hm j).stronglyMeasurable_mk.measurable, ?_, ?_⟩⟩
  · exact (hg j).1.congr_ae_on hU.measurableSet
      (Eventually.of_forall fun _ _ ↦ rfl) (he j)
  · exact (hg j).2.congr_ae_on (he j)

end EulerDipoleEigenvalues
