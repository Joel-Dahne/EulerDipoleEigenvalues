import NoEmbeddedEigenvalues.QuarterMeasureTransport
import NoEmbeddedEigenvalues.ACLWeakDerivative
import NoEmbeddedEigenvalues.WeakQuarterReconstruction

/-!
# Weak transport becomes a weak time derivative on a quarter strip

Blueprint: `lem:quarter-time-pullback`.

The orbit restriction theorem supplies one-dimensional ACL representatives.
Rectangular testing lifts their derivative identities to the single raw
pullback. Spatial L² data supply the local integrability through coarea.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- The weak transport derivative pulls back to the actual weak time derivative.
The spatial data are L² only on the bounded cell, not on the whole plane. -/
theorem HasWeakL0On.quarter_time {b : ℝ} (hb : b < 1)
    {U : Set (ℝ × ℝ)} {F D : ℝ × ℝ → ℂ}
    (hA : orbitAnnulus 0 b ⊆ U) (hd : HasWeakL0On U F D)
    (hmF : Measurable F) (hmD : Measurable D)
    (hF : MemLp F 2 (volume.restrict cellSquare))
    (hD : MemLp D 2 (volume.restrict cellSquare)) :
    HasWeakPartialOn (quarterOrbitStrip b) 1
      (fun q ↦ F (dipoleOrbit q.1 q.2)) (fun q ↦ D (dipoleOrbit q.1 q.2)) := by
  have hFp := memLp_comp_quarterOrbitStrip hb.le hmF hF
  have hDp := memLp_comp_quarterOrbitStrip hb.le hmD hD
  apply hasWeakPartialOn_of_locally
  intro q hq
  obtain ⟨a₀, c₀, m, hm, hqR, hRQ⟩ := quarterStrip_midpoint_rectangle hb.le hq
  let a := max a₀ (q.1 / 2)
  let c := min c₀ ((q.1 + b) / 2)
  have haq : a < q.1 := max_lt hqR.1.1 (by linarith [hq.1])
  have hqc : q.1 < c := lt_min hqR.1.2 (by linarith [hq.2.1])
  have ha : 0 < a := (half_pos hq.1).trans_le (le_max_right _ _)
  have hc : c < b := (min_le_right _ _).trans_lt (by linarith [hq.2.1])
  have hsub : Ioo a c ×ˢ Ioo (-m) m ⊆ quarterOrbitStrip b := by
    intro p hp
    exact hRQ ⟨⟨(le_max_left _ _).trans_lt hp.1.1,
      hp.1.2.trans_le (min_le_left _ _)⟩, hp.2⟩
  have hAsub : orbitAnnulus a c ⊆ U := fun p hp ↦
    hA ⟨hp.1, ⟨ha.trans hp.2.1, hp.2.2.trans hc⟩⟩
  have hsec := ae_orbit_restriction ha (haq.trans hqc) (hc.trans hb) hAsub hd
  let : IsFiniteMeasure (volume.restrict (Ioo a c ×ˢ Ioo (-m) m)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  refine ⟨Ioo a c ×ˢ Ioo (-m) m, isOpen_Ioo.prod isOpen_Ioo,
    ⟨⟨haq, hqc⟩, hqR.2⟩, ?_⟩
  apply hasWeakPartialOn_snd_of_ae_ac (by linarith)
    ((hFp.mono_measure (Measure.restrict_mono hsub le_rfl)).integrable (by norm_num))
    ((hDp.mono_measure (Measure.restrict_mono hsub le_rfl)).integrable (by norm_num))
  filter_upwards [hsec] with h hh
  obtain ⟨G, hGF, _, hAC, hder⟩ := hh
  exact ⟨G, hGF, hAC, hder⟩

end NoEmbeddedEigenvalues
