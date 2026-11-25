module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.InteriorTraceFlux

/-!
# Tangential weak differentiation of a continuous interior trace

Blueprint: `lem:tangential-interior-trace`.

A continuous potential with a tangential weak derivative having transverse H¹
regularity has an H¹ trace on each interior line. Its derivative is the canonical
trace of that specified tangential derivative. Only the indicated ordered mixed
derivative is used. No continuous gradient or raw gradient-line values occur.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter
open scoped Topology

/-- Differentiate the original continuous line restriction tangentially, using
the canonical transverse trace of its supplied weak derivative. The value norm
is recovered from the integral primitive, not assumed as an extra trace input. -/
theorem HasWeakPartialOn.trace_hasIntervalH1 {a b c d t : ℝ}
    {F D E : ℝ × ℝ → ℂ} (hab : a < b) (hcd : c < d) (ht : t ∈ Ioo c d)
    (hFc : ContinuousOn F (Ioo a b ×ˢ Ioo c d))
    (hF : MemLp F 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hD : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hE : MemLp E 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hx : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 0 F D)
    (hy : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 1 D E) :
    HasIntervalH1 a b (fun x ↦ F (x, t))
      (fun x ↦ interiorSectionTrace (fun s ↦ D (x, t + s))) := by
  obtain ⟨G, hGm, hGD, hG⟩ := hy.exists_acl_sections isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.2 hab) isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.2 hcd)
  have hFTC := hx.horizontal_integral_eq hab hcd hFc hF hD hGD hGm hG hE
  let T := fun x ↦ interiorSectionTrace (fun s ↦ D (x, t + s))
  have hTL : MemLp T 2 (volume.restrict (Ioo a b)) :=
    hy.memLp_interiorSectionTrace hab hcd ht hD hE
  have hTG : T =ᵐ[volume.restrict (Ioo a b)] (fun x ↦ G (x, t)) :=
    (hG.ae_interiorSectionTrace_eq hGD).mono fun x hx ↦ hx t ht
  have hFT : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b,
      (∫ s in x..y, T s) = F (y, t) - F (x, t) := by
    intro x hx y hy
    calc
      _ = ∫ s in x..y, G (s, t) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 hTG] with s hs hsI
        exact hs (uIoc_subset_uIcc.trans (ordConnected_Ioo.uIcc_subset hx hy) hsI)
      _ = _ := hFTC t ht x hx y hy
  let m := (a + b) / 2
  have hm : m ∈ Ioo a b := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  let P := fun x ↦ F (m, t) + ∫ s in m..x, T s
  have hPF : EqOn P (fun x ↦ F (x, t)) (Ioo a b) := by
    intro x hx
    dsimp only [P]
    rw [hFT m hm x hx]
    abel
  have hi : IntegrableOn T (Icc a b) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact hTL.integrable (by norm_num)
  have hu : IntervalIntegrable T volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).2 hi
  have hmU : m ∈ uIcc a b := by
    simpa only [uIcc_of_le hab.le] using Ioo_subset_Icc_self hm
  have hPc : ContinuousOn P (Icc a b) :=
    continuousOn_const.add (by simpa only [uIcc_of_le hab.le] using
      intervalIntegral.continuousOn_primitive_interval' hu hmU)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hPc
  have hPL : MemLp P 2 (volume.restrict (Ioo a b)) :=
    MemLp.of_bound ((hPc.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo) M
      ((ae_restrict_mem measurableSet_Ioo).mono fun x hx ↦ hM x (Ioo_subset_Icc_self hx))
  have hFL : MemLp (fun x ↦ F (x, t)) 2 (volume.restrict (Ioo a b)) :=
    hPL.ae_eq ((ae_restrict_mem measurableSet_Ioo).mono fun x hx ↦ hPF hx)
  obtain ⟨hac, hder⟩ := locally_ac_of_integral_eq hab hTL hFT
  exact ⟨hFL, hTL, hac, (ae_restrict_iff' measurableSet_Ioo).1 hder⟩

end EulerDipoleEigenvalues
