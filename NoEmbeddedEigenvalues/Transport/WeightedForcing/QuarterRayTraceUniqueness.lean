module

public import NoEmbeddedEigenvalues.Transport.WeightedGains.QuarterCoordinates
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Independence of canonical quarter-ray traces

Blueprint: `lem:quarter-ray-trace-unique`.

Two trace constructions on different open neighbourhoods agree on their common
ray interval. Compact radial segments admit a common transverse rectangle;
ACL trace independence and a countable rational interval cover give a.e. equality.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

theorem HasTransverseH1Trace.ae_eq {l r a b t : ℝ}
    {chart : ℝ × ℝ → ℝ × ℝ} {F : ℝ × ℝ → ℂ} {T S : ℝ → ℂ}
    (hT : HasTransverseH1Trace l r a b t chart F T)
    (hS : HasTransverseH1Trace l r a b t chart F S) :
    T =ᵐ[volume.restrict (Ioo l r)] S := by
  obtain ⟨_, hab, ht, G, D, _, hGF, hG, hD, hGD, hT⟩ := hT
  obtain ⟨_, _, _, H, E, _, hHF, hH, hE, hHE, hS⟩ := hS
  filter_upwards [hT, hS, hGD.ae_trace_independent hab hHE hGF hHF hG hH hD hE]
    with x hxT hxS hx
  exact hxT.trans ((hx t ht).trans hxS.symm)

/-- Canonical traces coincide on a common ray segment, even when their ambient
open neighbourhoods, transverse widths and derivative representatives differ. -/
theorem HasQuarterRayTrace.ae_eq {U V : Set (ℝ × ℝ)} (hU : IsOpen U) (hV : IsOpen V)
    {ρ ρ₁ ρ₂ : ℝ} {k : Fin 4} {side : Bool} {F : ℝ × ℝ → ℂ} {T S : ℝ → ℂ}
    (hT : HasQuarterRayTrace U ρ₁ k side F T)
    (hS : HasQuarterRayTrace V ρ₂ k side F S)
    (hρ₁ : ρ ≤ ρ₁) (hρ₂ : ρ ≤ ρ₂)
    (hray : rotatedQuarterEndpointRay k side '' Ioo 0 ρ ⊆ U ∩ V) :
    T =ᵐ[volume.restrict (Ioo 0 ρ)] S := by
  have hc : Continuous (rotatedQuarterEndpointChart k side) := by
    have hR : Continuous rotLift := by unfold rotLift; fun_prop
    apply (hR.iterate k.val).comp
    cases side <;> unfold quarterEndpointChart <;> dsimp <;> fun_prop
  have he (r : ℝ) : rotatedQuarterEndpointChart k side (r, 0) =
      rotatedQuarterEndpointRay k side r := by
    cases side <;> rfl
  have hlocal (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < ρ) :
      T =ᵐ[volume.restrict (Ioo a b)] S := by
    have hK : IsCompact (Icc a b ×ˢ ({0} : Set ℝ)) := isCompact_Icc.prod isCompact_singleton
    have hsub : Icc a b ×ˢ ({0} : Set ℝ) ⊆
        rotatedQuarterEndpointChart k side ⁻¹' (U ∩ V) := by
      rintro ⟨r, t⟩ ⟨hr, ht⟩
      have ht0 : t = 0 := ht
      subst t
      rw [mem_preimage, he]
      exact hray ⟨r, ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩, rfl⟩
    obtain ⟨w, hw, hwidth⟩ := hK.exists_cthickening_subset_open
      ((hU.inter hV).preimage hc) hsub
    have hrect : rotatedQuarterEndpointChart k side '' (Icc a b ×ˢ Icc (-w) w) ⊆ U ∩ V := by
      rintro _ ⟨q, hq, rfl⟩
      apply hwidth
      apply Metric.mem_cthickening_of_dist_le q (q.1, 0) w
        (Icc a b ×ˢ ({0} : Set ℝ)) ⟨hq.1, by simp⟩
      simp only [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero]
      exact max_le (le_of_lt hw) (abs_le.mpr hq.2)
    exact (hT a b ha hab (hb.trans_le hρ₁) w hw (hrect.trans inter_subset_left)).ae_eq
      (hS a b ha hab (hb.trans_le hρ₂) w hw (hrect.trans inter_subset_right))
  have hall : ∀ᵐ r : ℝ, ∀ a b : ℚ, 0 < (a : ℝ) → (a : ℝ) < b → (b : ℝ) < ρ →
      r ∈ Ioo (a : ℝ) b → T r = S r := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro b
    by_cases hh : 0 < (a : ℝ) ∧ (a : ℝ) < b ∧ (b : ℝ) < ρ
    · have h := (ae_restrict_iff' measurableSet_Ioo).1 (hlocal a b hh.1 hh.2.1 hh.2.2)
      exact h.mono fun _ hx _ _ _ hr ↦ hx hr
    · exact Eventually.of_forall fun _ ha hab hb _ ↦ (hh ⟨ha, hab, hb⟩).elim
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_Ioo] with r hr hrI
  obtain ⟨a, ha, har⟩ := exists_rat_btwn hrI.1
  obtain ⟨b, hrb, hb⟩ := exists_rat_btwn hrI.2
  exact hr a b ha (har.trans hrb) hb ⟨har, hrb⟩

end NoEmbeddedEigenvalues
