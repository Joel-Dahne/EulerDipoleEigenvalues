import NoEmbeddedEigenvalues.SobolevLocal
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Local Sobolev gluing on the plane

Blueprint: `lem:sobolev-local-gluing`.

Sobolev regularity can be checked on neighbourhoods of individual points. On a
relatively compact open set, choose a finite cover by precompact patches and a
smooth partition of unity. Each partitioned piece has compact support in a patch,
so the cutoff theorem puts it in global Hᵏ. Their finite sum represents the given
function on the relatively compact set. Domain-a.e. congruence allows each patch
to use its own representative; no pointwise matching on null sets is used.

This is gluing on the lift, separate from periodization to the torus.
-/

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set
open scoped ContDiff Manifold

/-- The zero function is in every integer-order local-domain Sobolev space. -/
theorem MemSobolevOn.zero (k : ℕ) (U : Set (ℝ × ℝ)) :
    MemSobolevOn k U (fun _ ↦ (0 : ℂ)) := by
  induction k with
  | zero => exact MemLp.zero'
  | succ k ih =>
    exact ⟨MemLp.zero', fun _ ↦
      ⟨_, ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, by simp⟩, ih⟩⟩

/-- A finite sum of Sobolev functions has the same Sobolev order. -/
theorem MemSobolevOn.finset_sum {ι : Type*} {k : ℕ} {U : Set (ℝ × ℝ)}
    {f : ι → ℝ × ℝ → ℂ} (s : Finset ι) (hf : ∀ i ∈ s, MemSobolevOn k U (f i)) :
    MemSobolevOn k U (fun p ↦ ∑ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MemSobolevOn.zero k U
  | @insert i s hi ih =>
    simpa only [MemSobolevOn, Finset.sum_insert hi] using
      MemSobolevOnWith.add (hf i (Finset.mem_insert_self i s))
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- Local Sobolev regularity can be checked in a neighbourhood of each point. -/
theorem memSobolevLocOn_of_locally {k : ℕ} {U : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℂ}
    (hloc : ∀ p ∈ U, ∃ W : Set (ℝ × ℝ), IsOpen W ∧ p ∈ W ∧
      MemSobolevLocOn k W f) : MemSobolevLocOn k U f := by
  classical
  intro V hV hc hVU
  have hpatch (p : closure V) : ∃ W : Set (ℝ × ℝ), IsOpen W ∧
      (p : ℝ × ℝ) ∈ W ∧ IsCompact (closure W) ∧ MemSobolevLocOn k W f := by
    obtain ⟨O, hO, hpO, hfO⟩ := hloc p (hVU p.property)
    obtain ⟨W, hW, hpW, hWO, hWc⟩ := exists_open_between_and_isCompact_closure
      isCompact_singleton hO (singleton_subset_iff.mpr hpO)
    refine ⟨W, hW, hpW (mem_singleton p.val), hWc, ?_⟩
    intro X hX hXc hXW
    exact hfO X hX hXc (hXW.trans (subset_closure.trans hWO))
  choose W hWo hpW hWc hfW using hpatch
  have hcover : closure V ⊆ ⋃ p, W p := fun p hp ↦
    mem_iUnion_of_mem ⟨p, hp⟩ (hpW ⟨p, hp⟩)
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover W hWo hcover
  have hcover' : closure V ⊆ ⋃ p : t, W p.val := by
    intro p hp
    obtain ⟨q, hqt, hpq⟩ := mem_iUnion₂.mp (ht hp)
    exact mem_iUnion_of_mem ⟨q, hqt⟩ hpq
  obtain ⟨ρ, hρ⟩ : ∃ ρ : SmoothPartitionOfUnity t 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (closure V),
      ρ.IsSubordinate (fun p ↦ W p.val) :=
    SmoothPartitionOfUnity.exists_isSubordinate _ isClosed_closure _
      (fun p ↦ hWo p.val) hcover'
  let χ (i : t) (p : ℝ × ℝ) : ℂ := (ρ i p : ℂ)
  have hχsub (i : t) : tsupport (χ i) ⊆ W i.val :=
    (tsupport_comp_subset Complex.ofReal_zero (ρ i)).trans (hρ i)
  have hχc (i : t) : HasCompactSupport (χ i) :=
    (hWc i.val).of_isClosed_subset (isClosed_tsupport _) ((hχsub i).trans subset_closure)
  have hpiece (i : t) : MemSobolevOn k univ (fun p ↦ χ i p * f p) := by
    apply (hfW i.val).cutoff k (hWo i.val) _ (hχc i) (hχsub i)
    exact Complex.ofRealCLM.contDiff.comp (ρ i).contMDiff.contDiff
  have hsum := MemSobolevOn.finset_sum Finset.univ (fun i _ ↦ hpiece i)
  apply (hsum.mono (subset_univ V)).congr_ae_on hV.measurableSet
  apply Filter.Eventually.of_forall
  intro p hp
  rw [← Finset.sum_mul]
  have hsumρ := ρ.sum_eq_one (subset_closure hp)
  simp only [finsum_eq_sum_of_fintype] at hsumρ
  have heq : ∑ i : t, χ i p = 1 := by
    simp only [χ, ← Complex.ofReal_sum, hsumρ, Complex.ofReal_one]
  rw [heq, one_mul]

/-- Local Sobolev representatives that agree a.e. with one function give local
Sobolev regularity of that function. Values on exceptional sets need not match. -/
theorem memSobolevLocOn_of_locally_ae {k : ℕ} {U : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℂ}
    (hloc : ∀ p ∈ U, ∃ W : Set (ℝ × ℝ), IsOpen W ∧ p ∈ W ∧
      ∃ g : ℝ × ℝ → ℂ, MemSobolevLocOn k W g ∧
        g =ᵐ[volume.restrict W] f) : MemSobolevLocOn k U f := by
  apply memSobolevLocOn_of_locally
  intro p hp
  obtain ⟨W, hW, hpW, g, hg, heq⟩ := hloc p hp
  exact ⟨W, hW, hpW, hg.congr_ae_on ((ae_restrict_iff' hW.measurableSet).mp heq)⟩

end NoEmbeddedEigenvalues
