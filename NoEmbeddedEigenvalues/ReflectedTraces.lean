import NoEmbeddedEigenvalues.TraceWeakGluing
import NoEmbeddedEigenvalues.AffineJets

/-!
# Reflection of canonical transverse traces

Blueprint: `lem:transverse-trace-reflection`.

Reflection transports actual L² norms and ordinary H¹ before a trace is
constructed. Almost-everywhere equality of the reflected spatial functions
then identifies the continuous section extensions, including their endpoint
values. No raw representative is evaluated on the reflecting line.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology

/-- The linear part of reflection in the normal coordinate. -/
def normalReflectionLinear : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ)

/-- Reflection `y ↦ c - y`, keeping the tangential coordinate fixed. -/
def normalReflection (c : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  planeAffine normalReflectionLinear (0, c)

@[simp] theorem normalReflection_apply (c : ℝ) (q : ℝ × ℝ) :
    normalReflection c q = (q.1, c - q.2) := by
  ext <;> simp [normalReflection, normalReflectionLinear, sub_eq_add_neg, add_comm]

theorem measurePreserving_normalReflection (c : ℝ) :
    MeasurePreserving (normalReflection c) volume volume := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (Measure.measurePreserving_sub_left volume c)
  rw [← Measure.volume_eq_prod] at h
  convert h using 1
  funext q
  exact normalReflection_apply c q

theorem normalReflection_preimage_rectangle (c l r a b : ℝ) :
    normalReflection c ⁻¹' (Ioo l r ×ˢ Ioo a b) =
      Ioo l r ×ˢ Ioo (c - b) (c - a) := by
  ext q
  simp only [mem_preimage, normalReflection_apply, mem_prod, mem_Ioo]
  constructor <;> rintro ⟨hx, hy, hz⟩ <;> exact ⟨hx, by linarith, by linarith⟩

/-- Changing the raw function or physical chart by a.e. equality of their actual
pullbacks leaves the canonical trace witnesses intact. -/
theorem HasTransverseH1Trace.congr_ae_pullback {l r a b t : ℝ}
    {C C' : ℝ × ℝ → ℝ × ℝ} {F F' : ℝ × ℝ → ℂ} {T : ℝ → ℂ}
    (h : HasTransverseH1Trace l r a b t C F T)
    (he : (F ∘ C) =ᵐ[volume.restrict (Ioo l r ×ˢ Ioo a b)] (F' ∘ C')) :
    HasTransverseH1Trace l r a b t C' F' T := by
  obtain ⟨hlr, hab, ht, G, D, hm, hGF, hG, hD, hGD, hT⟩ := h
  exact ⟨hlr, hab, ht, G, D, hm, hGF.trans he, hG, hD, hGD, hT⟩

/-- Canonical traces of two reflected a.e. pullbacks have the same character,
including when the normal point is an endpoint. -/
theorem HasTransverseH1Trace.ae_eq_reflected {l r a b t c : ℝ}
    {C C' : ℝ × ℝ → ℝ × ℝ} {F F' : ℝ × ℝ → ℂ} {T S : ℝ → ℂ} {χ : ℂ}
    (h : HasTransverseH1Trace l r a b t C F T)
    (h' : HasTransverseH1Trace l r (c - b) (c - a) (c - t) C' F' S)
    (he : (F' ∘ C') =ᵐ[volume.restrict (Ioo l r ×ˢ Ioo (c - b) (c - a))]
      (fun q ↦ χ * F (C (normalReflection c q)))) :
    S =ᵐ[volume.restrict (Ioo l r)] (fun s ↦ χ * T s) := by
  obtain ⟨_, hab, ht, G, D, _, hGF, hG, hD, hGD, hT⟩ := h
  obtain ⟨_, hba, ht', H, E, _, hHF, hH, hE, hHE, hS⟩ := h'
  have hm := (measurePreserving_normalReflection c).restrict_preimage
    (s := Ioo l r ×ˢ Ioo a b) (measurableSet_Ioo.prod measurableSet_Ioo)
  rw [normalReflection_preimage_rectangle] at hm
  have hGFref := hm.quasiMeasurePreserving.ae hGF
  have hHG : H =ᵐ[volume.restrict (Ioo l r ×ˢ Ioo (c - b) (c - a))]
      (fun q ↦ χ * G (normalReflection c q)) := by
    filter_upwards [hHF, he, hGFref] with q hq heq hgr
    exact hq.trans (heq.trans (congrArg (χ * ·) hgr.symm))
  have hprod : ∀ᵐ q ∂((volume.restrict (Ioo l r)).prod
      (volume.restrict (Ioo (c - b) (c - a)))),
      H q = χ * G (normalReflection c q) := by
    simpa only [Filter.EventuallyEq, Measure.prod_restrict, ← Measure.volume_eq_prod] using hHG
  filter_upwards [hT, hS, hGD.ae_hasIntervalH1 hG hD,
    hHE.ae_hasIntervalH1 hH hE, Measure.ae_ae_of_ae_prod hprod]
      with s hsT hsS hsG hsH hsEq
  have hmap : MapsTo (fun y ↦ c - y) (Icc (c - b) (c - a)) (Icc a b) := by
    intro y hy
    exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hmapo : MapsTo (fun y ↦ c - y) (Ioo (c - b) (c - a)) (Ioo a b) := by
    intro y hy
    exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hc : ContinuousOn (fun y ↦ χ * intervalH1Extension a b
      (fun z ↦ G (s, z)) (fun z ↦ D (s, z)) (c - y)) (Icc (c - b) (c - a)) :=
    continuousOn_const.mul ((hsG.continuousOn_extension hab).comp
      (continuous_const.sub continuous_id).continuousOn hmap)
  have hwhole := hsH.continuousOn_extension hba
  have heae : (intervalH1Extension (c - b) (c - a) (fun y ↦ H (s, y))
      (fun y ↦ E (s, y))) =ᵐ[volume.restrict (Ioo (c - b) (c - a))]
      (fun y ↦ χ * intervalH1Extension a b (fun z ↦ G (s, z))
        (fun z ↦ D (s, z)) (c - y)) := by
    filter_upwards [hsEq, ae_restrict_mem measurableSet_Ioo] with y hy hyI
    rw [hsH.extension_eq hba hyI, hsG.extension_eq hab (hmapo hyI)]
    simpa only [normalReflection_apply] using hy
  have hopen := Measure.eqOn_open_of_ae_eq heae isOpen_Ioo
    (hwhole.mono Ioo_subset_Icc_self) (hc.mono Ioo_subset_Icc_self)
  have hclosed := hopen.of_subset_closure hwhole hc Ioo_subset_Icc_self
    (by rw [closure_Ioo hba.ne])
  have hp := hclosed ht'
  rw [hsS, hsT]
  simpa only [aclTrace, sub_sub_cancel] using hp

/-- Reflection constructs both ordinary H¹ and the original trace with its
constant character. All norms are on the reflected bounded rectangle. -/
theorem HasTransverseH1Trace.reflect_normal {l r a b t c : ℝ}
    {C : ℝ × ℝ → ℝ × ℝ} {F : ℝ × ℝ → ℂ} {T : ℝ → ℂ}
    (h : HasTransverseH1Trace l r a b t C F T)
    (hF : MemSobolevOn 1 (Ioo l r ×ˢ Ioo a b) (F ∘ C)) (χ : ℂ) :
    let H := fun q ↦ χ * F (C (normalReflection c q))
    MemSobolevOn 1 (Ioo l r ×ˢ Ioo (c - b) (c - a)) H ∧
      HasTransverseH1Trace l r (c - b) (c - a) (c - t) id H (fun s ↦ χ * T s) := by
  let H := fun q ↦ χ * F (C (normalReflection c q))
  have hS := (hF.comp_planeAffine normalReflectionLinear (0, c)
    (measurePreserving_normalReflection c) (isOpen_Ioo.prod isOpen_Ioo)).const_mul χ
  change MemSobolevOn 1 (normalReflection c ⁻¹' (Ioo l r ×ˢ Ioo a b)) H at hS
  rw [normalReflection_preimage_rectangle] at hS
  have hba : c - b < c - a := by linarith [h.2.1]
  have ht : c - t ∈ Icc (c - b) (c - a) :=
    ⟨by linarith [h.2.2.1.2], by linarith [h.2.2.1.1]⟩
  obtain ⟨D, hd, hD⟩ := hS.2 1
  obtain ⟨G, hGm, hGH, hGD, _, _⟩ := hd.exists_l2_trace isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.2 h.1) hba hS.1 hD
  have hGL := hS.1.ae_eq hGH.symm
  have hR : HasTransverseH1Trace l r (c - b) (c - a) (c - t) id H
      (aclTrace (c - b) (c - a) G D (c - t)) :=
    ⟨h.1, hba, ht, G, D, hGm, hGH, hGL, hD, hGD, EventuallyEq.rfl⟩
  have he := h.ae_eq_reflected hR (χ := χ) (EventuallyEq.rfl)
  exact ⟨hS, h.1, hba, ht, G, D, hGm, hGH, hGL, hD, hGD, he.symm⟩

end NoEmbeddedEigenvalues
