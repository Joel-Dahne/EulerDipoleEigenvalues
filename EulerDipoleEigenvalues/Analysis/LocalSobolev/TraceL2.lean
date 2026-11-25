module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.ACLSlicing
public import EulerDipoleEigenvalues.Analysis.Inequalities.IntervalH1Estimates

/-!
# Elementary L² traces on a rectangle

Blueprint: `lem:trace-l2`.

Traces use the canonical continuous extension of almost every ACL section.
The endpoint values of a raw representative do not enter their definition.
The estimate follows from the one-dimensional FTC and Cauchy–Schwarz,
averaging over the bounded interval and then integrating over the other variable.
-/

@[expose] public section

noncomputable section

namespace EulerDipoleEigenvalues

open MeasureTheory Set Filter
open scoped Topology Interval

/-- A global increment bound on the canonical interval H¹ extension. -/
theorem HasIntervalH1.extension_sub_sq_le_global {a b x y : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖intervalH1Extension a b F D y - intervalH1Extension a b F D x‖ ^ 2 ≤
      (b - a) * ∫ t in Ioo a b, ‖D t‖ ^ 2 := by
  have hi := h.integrableOn_sq_norm_derivative
  have hordered : ∀ c ∈ Icc a b, ∀ d ∈ Icc a b, c ≤ d →
      ‖intervalH1Extension a b F D d - intervalH1Extension a b F D c‖ ^ 2 ≤
        (b - a) * ∫ t in Icc a b, ‖D t‖ ^ 2 := by
    intro c hc d hd hcd
    calc
      _ ≤ (d - c) * ∫ t in c..d, ‖D t‖ ^ 2 := h.extension_sub_sq_le hab hc hd hcd
      _ ≤ (b - a) * ∫ t in Icc a b, ‖D t‖ ^ 2 := by
        rw [intervalIntegral.integral_of_le hcd, ← integral_Icc_eq_integral_Ioc]
        exact mul_le_mul (by linarith [hc.1, hd.2])
          (setIntegral_mono_set hi (Eventually.of_forall (fun t ↦ sq_nonneg _))
            (Eventually.of_forall (fun t ht ↦ Icc_subset_Icc hc.1 hd.2 ht)))
          (integral_nonneg (fun t ↦ sq_nonneg _)) (by linarith)
  rw [← integral_Icc_eq_integral_Ioo]
  rcases le_total x y with hxy | hyx
  · exact hordered x hx y hy hxy
  · simpa only [norm_sub_rev] using hordered y hy x hx hyx

/-- The elementary trace estimate at every point of the closed interval. -/
theorem HasIntervalH1.extension_sq_le {a b t₀ : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b) (ht₀ : t₀ ∈ Icc a b) :
    ‖intervalH1Extension a b F D t₀‖ ^ 2 ≤
      (2 / (b - a)) * (∫ t in Ioo a b, ‖F t‖ ^ 2) +
        2 * (b - a) * ∫ t in Ioo a b, ‖D t‖ ^ 2 := by
  have hpoint : ∀ t ∈ Ioo a b, ‖intervalH1Extension a b F D t₀‖ ^ 2 ≤
      2 * ‖F t‖ ^ 2 + 2 * (b - a) * ∫ s in Ioo a b, ‖D s‖ ^ 2 := by
    intro t ht
    have hinc := h.extension_sub_sq_le_global hab (Ioo_subset_Icc_self ht) ht₀
    rw [h.extension_eq hab ht] at hinc
    have hn : ‖intervalH1Extension a b F D t₀‖ ≤
        ‖F t‖ + ‖intervalH1Extension a b F D t₀ - F t‖ := by
      simpa only [add_sub_cancel] using norm_add_le (F t) (intervalH1Extension a b F D t₀ - F t)
    have hs := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hn
    nlinarith [sq_nonneg (‖F t‖ - ‖intervalH1Extension a b F D t₀ - F t‖)]
  have hiF := h.memLp_value.norm.integrable_sq
  have havg := integral_mono_ae (integrable_const (‖intervalH1Extension a b F D t₀‖ ^ 2))
    ((hiF.const_mul 2).add (integrable_const
      (2 * (b - a) * ∫ t in Ioo a b, ‖D t‖ ^ 2)))
    ((ae_restrict_mem measurableSet_Ioo).mono fun t ht ↦ hpoint t ht)
  simp only [Pi.add_apply] at havg
  simp only [integral_add (hiF.const_mul 2) (integrable_const _), integral_const_mul,
    integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le), smul_eq_mul] at havg
  calc
    _ ≤ (2 * (∫ t in Ioo a b, ‖F t‖ ^ 2) +
        (b - a) * (2 * (b - a) * ∫ t in Ioo a b, ‖D t‖ ^ 2)) / (b - a) :=
      (le_div_iff₀ (sub_pos.mpr hab)).2 (by nlinarith [havg])
    _ = _ := by field_simp

/-- The canonical extension realizes the finite one-sided endpoint limits (and
agrees with the section at every interior point). -/
theorem HasIntervalH1.tendsto_extension {a b t₀ : ℝ} {F D : ℝ → ℂ}
    (h : HasIntervalH1 a b F D) (hab : a < b) (ht₀ : t₀ ∈ Icc a b) :
    Tendsto F (𝓝[Ioo a b] t₀) (𝓝 (intervalH1Extension a b F D t₀)) := by
  have ht := (h.continuousOn_extension hab t₀ ht₀).mono Ioo_subset_Icc_self
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact h.extension_eq hab ht

/-- Square-integrable functions on a product have square-integrable sections. -/
theorem ae_memLp_sections {I J : Set ℝ} {F : ℝ × ℝ → ℂ}
    (hF : MemLp F 2 (volume.restrict (I ×ˢ J))) :
    ∀ᵐ a ∂(volume.restrict I), MemLp (fun t ↦ F (a, t)) 2 (volume.restrict J) := by
  have hp : MemLp F 2 ((volume.restrict I).prod (volume.restrict J)) := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hF
  filter_upwards [hp.aestronglyMeasurable.prodMk_left,
    hp.norm.integrable_sq.prod_right_ae] with a ham hai
  exact (memLp_two_iff_integrable_sq_norm ham).2 hai

/-- Almost every ACL section is a bounded-interval H¹ representative. -/
theorem HasACLSectionsOn.ae_hasIntervalH1 {I : Set ℝ} {b₁ b₂ : ℝ} {G D : ℝ × ℝ → ℂ}
    (h : HasACLSectionsOn I (Ioo b₁ b₂) G D)
    (hG : MemLp G 2 (volume.restrict (I ×ˢ Ioo b₁ b₂)))
    (hD : MemLp D 2 (volume.restrict (I ×ˢ Ioo b₁ b₂))) :
    ∀ᵐ a ∂(volume.restrict I), HasIntervalH1 b₁ b₂ (fun t ↦ G (a, t)) (fun t ↦ D (a, t)) := by
  filter_upwards [h, ae_memLp_sections hG, ae_memLp_sections hD] with a ha haG haD
  refine ⟨haG, haD, ?_, (ae_restrict_iff' measurableSet_Ioo).1 ha.2⟩
  intro c d hc hcd hd
  exact ha.1 c d (by rw [uIcc_of_le hcd]; exact Icc_subset_Ioo hc hd)

/-- The trace at `t₀`, including the canonical endpoint values. The values on
exceptional sections are immaterial; a raw boundary assignment is never used. -/
def aclTrace (b₁ b₂ : ℝ) (G D : ℝ × ℝ → ℂ) (t₀ : ℝ) (a : ℝ) : ℂ :=
  intervalH1Extension b₁ b₂ (fun t ↦ G (a, t)) (fun t ↦ D (a, t)) t₀

/-- Measurability of the canonical trace, including at the endpoints. -/
theorem aestronglyMeasurable_aclTrace {I : Set ℝ} {b₁ b₂ t₀ : ℝ} {G D : ℝ × ℝ → ℂ}
    (hb : b₁ < b₂) (ht₀ : t₀ ∈ Icc b₁ b₂) (hG : Measurable G)
    (hD : MemLp D 2 (volume.restrict (I ×ˢ Ioo b₁ b₂))) :
    AEStronglyMeasurable (aclTrace b₁ b₂ G D t₀) (volume.restrict I) := by
  have hDc : AEStronglyMeasurable D
      ((volume.restrict I).prod (volume.restrict (Icc b₁ b₂))) := by
    have hp : AEStronglyMeasurable D
        ((volume.restrict I).prod (volume.restrict (Ioo b₁ b₂))) := by
      simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hD.aestronglyMeasurable
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hp
  have hm : (b₁ + b₂) / 2 ∈ Icc b₁ b₂ := ⟨by linarith, by linarith⟩
  have hint (c d : ℝ) (hc : c ∈ Icc b₁ b₂) (hd : d ∈ Icc b₁ b₂) :
      AEStronglyMeasurable (fun a ↦ ∫ t in Ioc c d, D (a, t)) (volume.restrict I) := by
    have h := hDc.mono_measure (Measure.prod_mono le_rfl
      (Measure.restrict_mono (Ioc_subset_Icc_self.trans (Icc_subset_Icc hc.1 hd.2)) le_rfl))
    exact h.integral_prod_right'
  have hmG : Measurable (fun a ↦ G (a, (b₁ + b₂) / 2)) :=
    hG.comp (measurable_id.prodMk measurable_const)
  exact hmG.aestronglyMeasurable.add ((hint _ _ hm ht₀).sub (hint _ _ ht₀ hm))

/-- The L² trace estimate, uniformly for every interior or endpoint trace. -/
theorem HasACLSectionsOn.l2_trace {I : Set ℝ} {b₁ b₂ : ℝ} {G D : ℝ × ℝ → ℂ}
    (h : HasACLSectionsOn I (Ioo b₁ b₂) G D) (hb : b₁ < b₂) (hGm : Measurable G)
    (hG : MemLp G 2 (volume.restrict (I ×ˢ Ioo b₁ b₂)))
    (hD : MemLp D 2 (volume.restrict (I ×ˢ Ioo b₁ b₂))) :
    ∀ t₀ ∈ Icc b₁ b₂,
      MemLp (aclTrace b₁ b₂ G D t₀) 2 (volume.restrict I) ∧
      (∫ a in I, ‖aclTrace b₁ b₂ G D t₀ a‖ ^ 2) ≤
        (2 / (b₂ - b₁)) * (∫ p in I ×ˢ Ioo b₁ b₂, ‖G p‖ ^ 2) +
          2 * (b₂ - b₁) * ∫ p in I ×ˢ Ioo b₁ b₂, ‖D p‖ ^ 2 := by
  intro t₀ ht₀
  have hGp : MemLp G 2 ((volume.restrict I).prod (volume.restrict (Ioo b₁ b₂))) := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hG
  have hDp : MemLp D 2 ((volume.restrict I).prod (volume.restrict (Ioo b₁ b₂))) := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hD
  have iG := hGp.norm.integrable_sq
  have iD := hDp.norm.integrable_sq
  have iB := (iG.integral_prod_left.const_mul (2 / (b₂ - b₁))).add
    (iD.integral_prod_left.const_mul (2 * (b₂ - b₁)))
  have hpt : ∀ᵐ a ∂(volume.restrict I), ‖aclTrace b₁ b₂ G D t₀ a‖ ^ 2 ≤
      (2 / (b₂ - b₁)) * (∫ t in Ioo b₁ b₂, ‖G (a, t)‖ ^ 2) +
        2 * (b₂ - b₁) * ∫ t in Ioo b₁ b₂, ‖D (a, t)‖ ^ 2 := by
    filter_upwards [h.ae_hasIntervalH1 hG hD] with a ha
    exact ha.extension_sq_le hb ht₀
  have htm := aestronglyMeasurable_aclTrace hb ht₀ hGm hD
  have iT : Integrable (fun a ↦ ‖aclTrace b₁ b₂ G D t₀ a‖ ^ 2) (volume.restrict I) := by
    apply iB.mono' (htm.norm.pow 2)
    filter_upwards [hpt] with a ha
    simpa only [Pi.pow_apply, Pi.add_apply, norm_pow, norm_norm] using ha
  refine ⟨(memLp_two_iff_integrable_sq_norm htm).2 iT, ?_⟩
  have hi := integral_mono_ae iT iB hpt
  simp only [Pi.add_apply] at hi
  rw [integral_add (iG.integral_prod_left.const_mul _) (iD.integral_prod_left.const_mul _),
    integral_const_mul, integral_const_mul, ← integral_prod _ iG, ← integral_prod _ iD] at hi
  simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hi

/-- On almost every section all interior traces are the section's actual values. -/
theorem HasACLSectionsOn.ae_trace_eq {I : Set ℝ} {b₁ b₂ : ℝ} {G D : ℝ × ℝ → ℂ}
    (h : HasACLSectionsOn I (Ioo b₁ b₂) G D) (hb : b₁ < b₂)
    (hG : MemLp G 2 (volume.restrict (I ×ˢ Ioo b₁ b₂)))
    (hD : MemLp D 2 (volume.restrict (I ×ˢ Ioo b₁ b₂))) :
    ∀ᵐ a ∂(volume.restrict I), ∀ t ∈ Ioo b₁ b₂, aclTrace b₁ b₂ G D t a = G (a, t) := by
  filter_upwards [h.ae_hasIntervalH1 hG hD] with a ha
  exact ha.extension_eq hb

/-- The endpoint traces are finite one-sided limits, not raw boundary values. -/
theorem HasACLSectionsOn.ae_tendsto_trace {I : Set ℝ} {b₁ b₂ : ℝ} {G D : ℝ × ℝ → ℂ}
    (h : HasACLSectionsOn I (Ioo b₁ b₂) G D) (hb : b₁ < b₂)
    (hG : MemLp G 2 (volume.restrict (I ×ˢ Ioo b₁ b₂)))
    (hD : MemLp D 2 (volume.restrict (I ×ˢ Ioo b₁ b₂))) :
    ∀ᵐ a ∂(volume.restrict I), ∀ t₀ ∈ Icc b₁ b₂,
      Tendsto (fun t ↦ G (a, t)) (𝓝[Ioo b₁ b₂] t₀) (𝓝 (aclTrace b₁ b₂ G D t₀ a)) := by
  filter_upwards [h.ae_hasIntervalH1 hG hD] with a ha
  exact fun t₀ ht₀ ↦ ha.tendsto_extension hb ht₀

/-- All closed-interval traces agree on almost every entire section, even for
different ACL representatives and different representatives of the derivative. -/
theorem HasACLSectionsOn.ae_trace_independent {I : Set ℝ} {b₁ b₂ : ℝ}
    {F G H D E : ℝ × ℝ → ℂ} (hb : b₁ < b₂)
    (hG : HasACLSectionsOn I (Ioo b₁ b₂) G D)
    (hH : HasACLSectionsOn I (Ioo b₁ b₂) H E)
    (hGF : G =ᵐ[volume.restrict (I ×ˢ Ioo b₁ b₂)] F)
    (hHF : H =ᵐ[volume.restrict (I ×ˢ Ioo b₁ b₂)] F)
    (hGL : MemLp G 2 (volume.restrict (I ×ˢ Ioo b₁ b₂)))
    (hHL : MemLp H 2 (volume.restrict (I ×ˢ Ioo b₁ b₂)))
    (hD : MemLp D 2 (volume.restrict (I ×ˢ Ioo b₁ b₂)))
    (hE : MemLp E 2 (volume.restrict (I ×ˢ Ioo b₁ b₂))) :
    ∀ᵐ a ∂(volume.restrict I), ∀ t₀ ∈ Icc b₁ b₂,
      aclTrace b₁ b₂ G D t₀ a = aclTrace b₁ b₂ H E t₀ a := by
  filter_upwards [hG.ae_hasIntervalH1 hGL hD, hH.ae_hasIntervalH1 hHL hE,
    hG.ae_eqOn isOpen_Ioo hH hGF hHF] with a haG haH heq
  intro t₀ ht₀
  exact (haG.extension_unique hb (haH.continuousOn_extension hb)
    (fun t ht ↦ (haH.extension_eq hb ht).trans (heq t ht).symm) ht₀).symm

/-- Directional weak derivatives in L² have canonical L² traces on every line
of the closed strip (`lem:trace-l2`). The first interval may be unbounded.
Endpoint limits and independence of representatives are supplied by
`HasACLSectionsOn.ae_tendsto_trace` and `HasACLSectionsOn.ae_trace_independent`. -/
theorem HasWeakPartialOn.exists_l2_trace {I : Set ℝ} {b₁ b₂ : ℝ} {F D : ℝ × ℝ → ℂ}
    (hI : IsOpen I) (hIc : OrdConnected I) (hIn : I.Nonempty) (hb : b₁ < b₂)
    (hd : HasWeakPartialOn (I ×ˢ Ioo b₁ b₂) 1 F D)
    (hF : MemLp F 2 (volume.restrict (I ×ˢ Ioo b₁ b₂)))
    (hD : MemLp D 2 (volume.restrict (I ×ˢ Ioo b₁ b₂))) :
    ∃ G : ℝ × ℝ → ℂ, Measurable G ∧
      G =ᵐ[volume.restrict (I ×ˢ Ioo b₁ b₂)] F ∧
      HasACLSectionsOn I (Ioo b₁ b₂) G D ∧
      (∀ᵐ a ∂(volume.restrict I), HasIntervalH1 b₁ b₂ (fun t ↦ G (a, t)) (fun t ↦ D (a, t))) ∧
      ∀ t₀ ∈ Icc b₁ b₂,
        MemLp (aclTrace b₁ b₂ G D t₀) 2 (volume.restrict I) ∧
        (∫ a in I, ‖aclTrace b₁ b₂ G D t₀ a‖ ^ 2) ≤
          (2 / (b₂ - b₁)) * (∫ p in I ×ˢ Ioo b₁ b₂, ‖F p‖ ^ 2) +
            2 * (b₂ - b₁) * ∫ p in I ×ˢ Ioo b₁ b₂, ‖D p‖ ^ 2 := by
  obtain ⟨G, hGm, hGF, hG⟩ := hd.exists_acl_sections hI hIc hIn
    isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.2 hb)
  have hGL : MemLp G 2 (volume.restrict (I ×ˢ Ioo b₁ b₂)) := hF.ae_eq hGF.symm
  refine ⟨G, hGm, hGF, hG, hG.ae_hasIntervalH1 hGL hD, fun t₀ ht₀ ↦ ?_⟩
  obtain ⟨hTL, hT⟩ := hG.l2_trace hb hGm hGL hD t₀ ht₀
  refine ⟨hTL, ?_⟩
  have hi : (∫ p in I ×ˢ Ioo b₁ b₂, ‖G p‖ ^ 2) =
      ∫ p in I ×ˢ Ioo b₁ b₂, ‖F p‖ ^ 2 :=
    integral_congr_ae (hGF.mono fun p hp ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hp)
  rwa [hi] at hT

end EulerDipoleEigenvalues
