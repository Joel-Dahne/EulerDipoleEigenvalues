import NoEmbeddedEigenvalues.MixedStaticForm
import NoEmbeddedEigenvalues.CosineTraceHardy

/-! # Pairing quotient trace masses before taking cutoffs -/

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter ComplexConjugate
open scoped ENNReal

local notation "c" => (Real.pi / 2)

private def mass (T : ℝ → ℂ) (x : ℝ) : ℂ := T x * conj (T x)

private theorem mass_ac {T : ℝ → ℂ} (hT : AbsolutelyContinuousOnInterval T (-c) c) :
    AbsolutelyContinuousOnInterval (mass T) (-c) c :=
  hT.fun_smul
    (Complex.conjCLE.toContinuousLinearMap.lipschitzWith.comp_absolutelyContinuousOnInterval hT)

private theorem mass_deriv_memLp {T : ℝ → ℂ} (hT : AbsolutelyContinuousOnInterval T (-c) c)
    (hD : MemLp (deriv T) 2 (volume.restrict (Ioo (-c) c))) :
    MemLp (deriv (mass T)) 2 (volume.restrict (Ioo (-c) c)) := by
  let μ := volume.restrict (Ioo (-c) c)
  obtain ⟨M, hM⟩ := hT.exists_bound
  have hmem : ∀ᵐ x ∂μ, x ∈ Ioo (-c) c := ae_restrict_mem measurableSet_Ioo
  have hbound : ∀ᵐ x ∂μ, ‖T x‖ ≤ M := hmem.mono fun x hx ↦
    hM x (Icc_subset_uIcc (Ioo_subset_Icc_self hx))
  have hm := ((hT.continuousOn.mono (Ioo_subset_Icc_self.trans
    (Icc_subset_uIcc : Icc (-c) c ⊆ uIcc (-c) c))).aestronglyMeasurable
      (μ := volume) measurableSet_Ioo)
  have hTtop : MemLp T ∞ μ := memLp_top_of_bound hm M hbound
  have hconj {F : ℝ → ℂ} {p : ENNReal} (hf : MemLp F p μ) :
      MemLp (fun x ↦ conj (F x)) p μ :=
    hf.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
      (.of_forall fun x ↦ (Complex.norm_conj (F x)).symm)
  have h := (hD.mul (r := 2) (hconj hTtop)).add (hTtop.mul (r := 2) (hconj hD))
  apply h.ae_eq
  filter_upwards [hmem,
    ae_restrict_of_ae (s := Ioo (-c) c) hT.boundedVariationOn.ae_differentiableAt_of_mem_uIcc]
    with x hx hd
  have ht := (hd (Icc_subset_uIcc (Ioo_subset_Icc_self hx))).hasDerivAt
  have htc := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt x ht
  exact (ht.mul htc).deriv.symm

/-- The combined Dirichlet-minus-Neumann squared quotient on a shared straight
edge parameter. After summing the two edges of each type, this vanishes at
both endpoints, where the two corner sums agree. -/
def mixedEdgeMassDefect (φ : ℝ × ℝ → ℂ) (x : ℝ) : ℝ :=
  (‖φ (cellEdgeNormal true, x)‖ ^ 2 + ‖φ (cellEdgeNormal false, x)‖ ^ 2) -
    (‖φ (x, cellEdgeNormal true)‖ ^ 2 + ‖φ (x, cellEdgeNormal false)‖ ^ 2)

/-- The combined trace mass, unlike the individual edge masses, is integrable
in flow-time measure (da/\cos a). -/
theorem mixed_edge_mass_defect_integrable {ω : L2} (d : MixedQuotientData ω) :
    IntegrableOn (fun x ↦ mixedEdgeMassDefect d.phi x / Real.cos x) (Ioo (-c) c) := by
  let T (j : Fin 2) (σ : Bool) := fun a ↦ d.phi (traceSideCoords j (a, cellEdgeNormal σ))
  let F (x : ℝ) := (mass (T 1 true) x + mass (T 1 false) x) -
    (mass (T 0 true) x + mass (T 0 false) x)
  have ha (j : Fin 2) (σ : Bool) : AbsolutelyContinuousOnInterval (mass (T j σ)) (-c) c :=
    mass_ac (by simpa only [neg_div] using (mixed_quotient_side_traces d j σ).1)
  have hDa (j : Fin 2) (σ : Bool) :
      MemLp (deriv (mass (T j σ))) 2 (volume.restrict (Ioo (-c) c)) :=
    mass_deriv_memLp
      (by simpa only [neg_div] using (mixed_quotient_side_traces d j σ).1)
      (by simpa only [neg_div] using (mixed_quotient_side_traces d j σ).2.1)
  have hF : AbsolutelyContinuousOnInterval F (-c) c :=
    ((ha 1 true).add (ha 1 false)).sub ((ha 0 true).add (ha 0 false))
  have hD : MemLp (deriv F) 2 (volume.restrict (Ioo (-c) c)) := by
    have hd (j : Fin 2) (σ : Bool) :=
      ae_restrict_of_ae (s := Ioo (-c) c)
        (ha j σ).boundedVariationOn.ae_differentiableAt_of_mem_uIcc
    apply (((hDa 1 true).add (hDa 1 false)).sub ((hDa 0 true).add (hDa 0 false))).ae_eq
    filter_upwards [ae_restrict_mem (s := Ioo (-c) c) measurableSet_Ioo,
      hd 1 true, hd 1 false, hd 0 true, hd 0 false] with x hx h₁ h₂ h₃ h₄
    have hx' := Icc_subset_uIcc (Ioo_subset_Icc_self hx)
    exact (((h₁ hx').hasDerivAt.add (h₂ hx').hasDerivAt).sub
      ((h₃ hx').hasDerivAt.add (h₄ hx').hasDerivAt)).deriv.symm
  have hzero (σ : Bool) : F (cellEdgeNormal σ) = 0 := by
    have hm (u v : ℂ) : u = v → u - v = 0 := fun h ↦ sub_eq_zero.mpr h
    apply hm
    have hab : -c < c := by linarith [Real.pi_pos]
    have hq : ((-c, c) : ℝ × ℝ) ∈ closure mixedOpenCell := by
      rw [mixedOpenCell, closure_prod_eq, closure_Ioo (by simpa only [neg_div] using hab.ne)]
      exact ⟨⟨by linarith, hab.le⟩, ⟨by linarith [hab], le_rfl⟩⟩
    have ho : d.phi (c, -c) = -d.phi (-c, c) := by
      have h := d.central_odd (-c, c) hq
      change d.phi (-(-c), -c) = _ at h
      rwa [neg_neg] at h
    cases σ <;>
      simp only [T, traceSideCoords, one_ne_zero, ite_false, ite_true, mass, Prod.swap,
        cellEdgeNormal, Bool.false_eq_true, ite_false, neg_div, ho, map_neg, neg_mul_neg]
  have hl : F (-c) = 0 := by simpa [cellEdgeNormal, neg_div] using hzero false
  have hr : F c = 0 := hzero true
  have he (z : ℂ) : z * conj z = (‖z‖ ^ 2 : ℝ) := by
    apply Complex.ext
    · rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re]
      ring
    · simp only [Complex.mul_im, Complex.conj_im, Complex.conj_re, Complex.ofReal_im]
      ring
  have hdiv : IntegrableOn (fun x ↦ F x / (Real.cos x : ℂ)) (Ioo (-c) c) :=
    (memLp_div_cos_of_ac hF hD hl hr).integrable (by norm_num)
  apply hdiv.re.congr
  filter_upwards with x
  change (F x / (Real.cos x : ℂ)).re = _
  simp only [F, T, mass, he, traceSideCoords, one_ne_zero, ite_false, ite_true,
    Complex.div_ofReal_re, Complex.add_re, Complex.sub_re, Complex.ofReal_re, mixedEdgeMassDefect]
  rfl

end NoEmbeddedEigenvalues
