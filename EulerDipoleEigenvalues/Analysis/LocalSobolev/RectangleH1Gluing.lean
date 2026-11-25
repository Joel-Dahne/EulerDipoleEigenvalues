module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.TraceWeakGluing
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Ordinary H¹ gluing from two matching canonical traces

Blueprint: `lem:rectangle-h1-gluing`.

The half-rectangle H¹ data supply finite derivative norms. Their piecewise
assembly is first proved square integrable on the whole rectangle; the null
joining line is omitted only in this norm argument. Matching canonical traces
then give genuine weak identities and the same full-window trace.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

private theorem memLp_rectangle_halves {l r a t b : ℝ} {F : ℝ × ℝ → ℂ}
    (hat : a < t) (htb : t < b)
    (hL : MemLp F 2 (volume.restrict (Ioo l r ×ˢ Ioo a t)))
    (hR : MemLp F 2 (volume.restrict (Ioo l r ×ˢ Ioo t b))) :
    MemLp F 2 (volume.restrict (Ioo l r ×ˢ Ioo a b)) := by
  have hsL : Ioo l r ×ˢ Ioo a t ⊆ Ioo l r ×ˢ Ioo a b :=
    prod_mono Subset.rfl (Ioo_subset_Ioo le_rfl htb.le)
  have hsR : Ioo l r ×ˢ Ioo t b ⊆ Ioo l r ×ˢ Ioo a b :=
    prod_mono Subset.rfl (Ioo_subset_Ioo hat.le le_rfl)
  have hiL : MemLp ((Ioo l r ×ˢ Ioo a t).indicator F) 2
      (volume.restrict (Ioo l r ×ˢ Ioo a b)) := by
    rw [memLp_indicator_iff_restrict (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet,
      Measure.restrict_restrict_of_subset hsL]
    exact hL
  have hiR : MemLp ((Ioo l r ×ˢ Ioo t b).indicator F) 2
      (volume.restrict (Ioo l r ×ˢ Ioo a b)) := by
    rw [memLp_indicator_iff_restrict (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet,
      Measure.restrict_restrict_of_subset hsR]
    exact hR
  have hne : ∀ᵐ p : ℝ × ℝ, p.2 ≠ t := by
    have hx : ∀ᵐ y : ℝ, y ≠ t := by
      simp only [ae_iff, not_not, ofPred_eq_eq_singleton, measure_singleton]
    exact Measure.quasiMeasurePreserving_snd.ae hx
  apply (hiL.add hiR).ae_eq
  filter_upwards [ae_restrict_of_ae hne, ae_restrict_mem
    (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp hpQ
  change (Ioo l r ×ˢ Ioo a t).indicator F p +
    (Ioo l r ×ˢ Ioo t b).indicator F p = F p
  rcases lt_or_gt_of_ne hp with hpt | htp
  · have hm : p ∈ Ioo l r ×ˢ Ioo a t := ⟨hpQ.1, hpQ.2.1, hpt⟩
    have hn : p ∉ Ioo l r ×ˢ Ioo t b := fun h ↦ lt_asymm hpt h.2.1
    simp [hm, hn]
  · have hm : p ∈ Ioo l r ×ˢ Ioo t b := ⟨hpQ.1, htp, hpQ.2.2⟩
    have hn : p ∉ Ioo l r ×ˢ Ioo a t := fun h ↦ lt_asymm htp h.2.2
    simp [hm, hn]

/-- Ordinary H¹ on the two halves plus the same canonical trace gives ordinary
H¹ on the whole rectangle and retains that trace. -/
theorem MemSobolevOn.glue_matching_trace {l r a t b : ℝ}
    {F : ℝ × ℝ → ℂ} {T : ℝ → ℂ}
    (hL : MemSobolevOn 1 (Ioo l r ×ˢ Ioo a t) F)
    (hR : MemSobolevOn 1 (Ioo l r ×ˢ Ioo t b) F)
    (htL : HasTransverseH1Trace l r a t t id F T)
    (htR : HasTransverseH1Trace l r t b t id F T) :
    MemSobolevOn 1 (Ioo l r ×ˢ Ioo a b) F ∧
      HasTransverseH1Trace l r a b t id F T := by
  choose DL hDL hDLL using hL.2
  choose DR hDR hDRL using hR.2
  let D := fun (j : Fin 2) (p : ℝ × ℝ) ↦ if p.2 < t then DL j p else DR j p
  have heL (j : Fin 2) : ∀ p ∈ Ioo l r ×ˢ Ioo a t, DL j p = D j p := by
    intro p hp
    simp [D, hp.2.2]
  have heR (j : Fin 2) : ∀ p ∈ Ioo l r ×ˢ Ioo t b, DR j p = D j p := by
    intro p hp
    simp [D, not_lt_of_gt hp.2.1]
  have hdL (j : Fin 2) : HasWeakPartialOn (Ioo l r ×ˢ Ioo a t) j F (D j) :=
    (hDL j).congr_ae_on (measurableSet_Ioo.prod measurableSet_Ioo)
      (Eventually.of_forall fun _ _ ↦ rfl) (Eventually.of_forall (heL j))
  have hdR (j : Fin 2) : HasWeakPartialOn (Ioo l r ×ˢ Ioo t b) j F (D j) :=
    (hDR j).congr_ae_on (measurableSet_Ioo.prod measurableSet_Ioo)
      (Eventually.of_forall fun _ _ ↦ rfl) (Eventually.of_forall (heR j))
  have hF := memLp_rectangle_halves htL.2.1 htR.2.1 hL.1 hR.1
  have hD (j : Fin 2) : MemLp (D j) 2 (volume.restrict (Ioo l r ×ˢ Ioo a b)) := by
    apply memLp_rectangle_halves htL.2.1 htR.2.1
    · exact (hDLL j).ae_eq ((ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)).mono
        fun p hp ↦ heL j p hp)
    · exact (hDRL j).ae_eq ((ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)).mono
        fun p hp ↦ heR j p hp)
  exact ⟨(htL.h1_glue htR hdL hdR hF hD).1,
    htL.glue_trace htR (hdL 1) (hdR 1) hF (hD 1)⟩

end EulerDipoleEigenvalues
