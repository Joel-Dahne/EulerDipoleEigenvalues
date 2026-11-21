module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.IntervalParameterH1

/-!
# A boundary-flux formula for weak parameter integrals

Blueprint: `lem:fixed-window-flux`.

A weak transverse derivative integrates to the boundary values of its original
continuous potential on almost every section. A divergence decomposition of a
weak parameter derivative therefore gives an H¹ derivative with boundary flux.
The window endpoints lie strictly inside the rectangle; no raw boundary trace
of a merely almost-everywhere defined function is evaluated.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology

/-- Transverse FTC for the original continuous function on almost every section. -/
theorem HasWeakPartialOn.ae_vertical_integral_eq {a b c d : ℝ} {F D : ℝ × ℝ → ℂ}
    (hab : a < b) (hcd : c < d)
    (hFc : ContinuousOn F (Ioo a b ×ˢ Ioo c d))
    (hF : MemLp F 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hD : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hd : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 1 F D) :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)), ∀ l ∈ Ioo c d, ∀ r ∈ Ioo c d,
      (∫ t in l..r, D (x, t)) = F (x, r) - F (x, l) := by
  obtain ⟨K, -, hKF, hK⟩ := hd.exists_acl_sections isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.2 hab) isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.2 hcd)
  have hcont : ∀ᵐ x ∂(volume.restrict (Ioo a b)),
      ContinuousOn (fun t ↦ F (x, t)) (Ioo c d) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hFc.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht ↦ ⟨hx, ht⟩)
  have heq := ae_eqOn_sections_of_ae_eq isOpen_Ioo hKF (hK.ae_continuousOn isOpen_Ioo) hcont
  filter_upwards [hK.ae_hasIntervalH1 (hF.ae_eq hKF.symm) hD, heq] with x hx hxe
  intro l hl r hr
  exact (hx.integral_eq_sub hl hr).trans (congrArg₂ Sub.sub (hxe r hr) (hxe l hl))

/-- Replacing the specified derivative almost everywhere preserves interval H¹. -/
theorem HasIntervalH1.congr_derivative {a b : ℝ} {F D E : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (he : D =ᵐ[volume.restrict (Ioo a b)] E) :
    HasIntervalH1 a b F E := by
  refine ⟨h.memLp_value, h.memLp_derivative.ae_eq he, h.locally_absolutelyContinuous, ?_⟩
  filter_upwards [h.hasDerivAt_ae, (ae_restrict_iff' measurableSet_Ioo).1 he] with x hx hxe hxI
  rw [← hxe hxI]
  exact hx hxI

/-- A divergence decomposition of a weak level derivative produces the actual
boundary-flux derivative of its fixed-window integral. The coefficient may
be arbitrary: the supplied L² fields already guarantee the required finiteness. -/
theorem HasWeakPartialOn.setIntegral_h1_flux {a b c d l r : ℝ}
    (hab : a < b) (hcd : c < d) (hl : c < l) (hlr : l ≤ r) (hr : r < d)
    {F D H P B : ℝ × ℝ → ℂ} {β : ℝ → ℂ}
    (hFc : ContinuousOn F (Ioo a b ×ˢ Ioo c d))
    (hPc : ContinuousOn P (Ioo a b ×ˢ Ioo c d))
    (hF : MemLp F 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hD : MemLp D 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hH : MemLp H 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hP : MemLp P 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hB : MemLp B 2 (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hx : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 0 F D)
    (ht : HasWeakPartialOn (Ioo a b ×ˢ Ioo c d) 1 P B)
    (hflux : ∀ q ∈ Ioo a b ×ˢ Ioo c d, D q = H q + β q.1 * B q) :
    HasIntervalH1 a b (fun x ↦ ∫ t in Icc l r, F (x, t))
      (fun x ↦ (∫ t in Icc l r, H (x, t)) + β x * (P (x, r) - P (x, l))) := by
  have hN := hx.setIntegral_h1 hab hcd hl hlr hr hFc hF hD
  have hsub : Icc l r ⊆ Ioo c d := Icc_subset_Ioo hl hr
  have hEq : (fun x ↦ ∫ t in Icc l r, D (x, t)) =ᵐ[volume.restrict (Ioo a b)]
      (fun x ↦ (∫ t in Icc l r, H (x, t)) + β x * (P (x, r) - P (x, l))) := by
    filter_upwards [ht.ae_vertical_integral_eq hab hcd hPc hP hB,
      ae_memLp_sections hH, ae_memLp_sections hB, ae_restrict_mem measurableSet_Ioo]
      with x hFTC hHx hBx hxI
    have hHi : IntegrableOn (fun t ↦ H (x, t)) (Icc l r) :=
      (hHx.mono_measure (Measure.restrict_mono hsub le_rfl)).integrable (by norm_num)
    have hBi : IntegrableOn (fun t ↦ B (x, t)) (Icc l r) :=
      (hBx.mono_measure (Measure.restrict_mono hsub le_rfl)).integrable (by norm_num)
    calc
      _ = ∫ t in Icc l r, H (x, t) + β x * B (x, t) :=
        setIntegral_congr_fun measurableSet_Icc (fun t ht ↦ hflux (x, t) ⟨hxI, hsub ht⟩)
      _ = (∫ t in Icc l r, H (x, t)) + β x * ∫ t in Icc l r, B (x, t) := by
        rw [integral_add hHi (hBi.const_mul _), integral_const_mul]
      _ = _ := by
        have hs : (∫ t in Icc l r, B (x, t)) = P (x, r) - P (x, l) := by
          rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlr]
          exact hFTC l ⟨hl, hlr.trans_lt hr⟩ r ⟨hl.trans_le hlr, hr⟩
        rw [hs]
  exact hN.congr_derivative hEq

end NoEmbeddedEigenvalues
