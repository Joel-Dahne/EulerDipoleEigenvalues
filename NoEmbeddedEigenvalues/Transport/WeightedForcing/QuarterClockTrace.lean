module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.ClockEndpointTrace

/-! # Canonical quarter endpoint traces from physical-time energy -/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- Actual joint physical-time H1 energy controls both canonical quarter
endpoint traces. Local normalized weak data identify the same germ, not a raw
null-ray value. -/
theorem memLp_quarter_clock_trace {r : ℝ}
    {F H : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (quarterOrbitStrip r)))
    (hH : MemLp H 2 (volume.restrict (quarterOrbitStrip r)))
    (hS : ∀ h ∈ Ioo 0 r, 4 ≤ orbitPeriod h)
    (hloc : ∀ a b : ℝ, 0 < a → a < b → b < r →
      let R := Ioo a b ×ˢ Ioo (-1 / 4 : ℝ) (3 / 4)
      let Fn := fun q : ℝ × ℝ ↦ F (q.1, q.2 * orbitPeriod q.1)
      let Hn := fun q : ℝ × ℝ ↦ (orbitPeriod q.1 : ℂ) * H (q.1, q.2 * orbitPeriod q.1)
      HasWeakPartialOn R 1 Fn Hn ∧ MemLp Fn 2 (volume.restrict R) ∧
        MemLp Hn 2 (volume.restrict R)) (side : Bool) :
    MemLp (fun h ↦ interiorSectionTrace (fun s ↦
      F (h, ((if side then 1 else -1 : ℝ) / 8 + s) * orbitPeriod h))) 2
      (volume.restrict (Ioo 0 r)) := by
  let E := fun h ↦ 2 * (∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), ‖F (h, t)‖ ^ 2) +
    2 * (∫ t in Ioo (-eighthPeriod h) (eighthPeriod h), ‖H (h, t)‖ ^ 2)
  have hEf := integrable_quarterStrip_sections (hF.integrable_norm_pow (by norm_num))
  have hEh := integrable_quarterStrip_sections (hH.integrable_norm_pow (by norm_num))
  apply memLp_two_of_local_sq_bound (E := E) ((hEf.1.const_mul 2).add (hEh.1.const_mul 2))
  intro a b ha hab hb
  obtain ⟨hd, hFn, hHn⟩ := hloc a b ha hab hb
  let θ : ℝ := (if side then 1 else -1) / 8
  have hθ : θ ∈ Ioo (-1 / 4 : ℝ) (3 / 4) := by cases side <;> norm_num [θ]
  have hT := HasWeakPartialOn.memLp_interiorSectionTrace hab (by norm_num) hθ hFn hHn hd
  refine ⟨hT, ?_⟩
  obtain ⟨G, _, hGe, hGa⟩ := hd.exists_acl_sections isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.2 hab) isOpen_Ioo ordConnected_Ioo (by norm_num)
  have hGL := hFn.ae_eq hGe.symm
  filter_upwards [hGa.ae_hasIntervalH1 hGL hHn,
    ae_sections_eq_of_rectangle hGe, ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo ha.le hb.le) hEf.2,
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo ha.le hb.le) hEh.2]
    with h hh he hI _ _
  have hs := hS h ⟨ha.trans hI.1, hI.2.trans hb⟩
  have ht := clock_endpoint_trace_sq_le (F := fun t ↦ F (h, t))
    (H := fun t ↦ H (h, t)) hs hh he side
  simpa only [E, orbitPeriod,
    show -(8 * eighthPeriod h) / 8 = -eighthPeriod h by ring,
    show 8 * eighthPeriod h / 8 = eighthPeriod h by ring] using ht

end NoEmbeddedEigenvalues
