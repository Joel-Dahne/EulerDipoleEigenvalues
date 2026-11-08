import NoEmbeddedEigenvalues.EvenEvenBoundary

/-!
# Diagonal Hardy estimates for even torus functions

The normal diagonal derivatives are odd across the separatrix lines. ACL
representatives turn this symmetry into zero traces. The primitive Hardy
estimate then controls division by the corresponding diagonal cosine.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Topology Real
open scoped ENNReal

private theorem inv_sin_sq_bound {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (π / 2)) :
    1 / sin t ^ 2 ≤ (π / 2) ^ 2 / t ^ 2 := by
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [pi_pos, ht.2])
  have hb : t ≤ (π / 2) * sin t := by
    have hh := mul_le_sin ht.1.le ht.2.le
    have hp := mul_le_mul_of_nonneg_left hh (show 0 ≤ π / 2 by positivity)
    field_simp at hp
    nlinarith
  apply (div_le_div_iff₀ (sq_pos_of_pos hs) (sq_pos_of_pos ht.1)).mpr
  nlinarith [sq_le_sq₀ ht.1.le (by positivity : 0 ≤ π / 2 * sin t) |>.mpr hb]

private theorem interval_cos_hardy {F D : ℝ → ℂ}
    (hF : HasIntervalH1 (-2 * π) (2 * π) F D)
    (hodd : ∀ t ∈ Ioo (0 : ℝ) π, F (π - t) = -F t)
    (hzero : F (-π / 2) = 0) :
    (∫⁻ t in Ioo (-π / 2) (π / 2), ENNReal.ofReal (‖F t‖ ^ 2 / cos t ^ 2)) ≤
      (2 * (ENNReal.ofReal ((π / 2) ^ 2) * 4)) *
        ∫⁻ t in Ioo (-2 * π) (2 * π), ENNReal.ofReal (‖D t‖ ^ 2) := by
  simp only [neg_div] at hzero ⊢
  let c := π / 2
  let E := ∫⁻ t in Ioo (-2 * π) (2 * π), ENNReal.ofReal (‖D t‖ ^ 2)
  let H := fun t ↦ ENNReal.ofReal (‖F t‖ ^ 2 / cos t ^ 2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hz : F c = 0 := by
    have hh := hodd c ⟨hc, by dsimp [c]; linarith [pi_pos]⟩
    rw [show π - c = c by dsimp [c]; ring] at hh
    exact CharZero.eq_neg_self_iff.1 hh
  have hright (b : ℝ) (hb : b ∈ Ioo (-2 * π) (2 * π)) (hbc : c ≤ 2 * π - b) :
      (∫⁻ t in Ioo 0 c, ENNReal.ofReal (‖F (b + t) - F b‖ ^ 2 / t ^ 2)) ≤ 4 * E := by
    exact (lintegral_mono_set (Ioo_subset_Ioo le_rfl hbc)).trans
      ((hF.lintegral_sq_sub_div_sq_le hb).trans (by
        dsimp [E]
        gcongr
        exact hb.1.le))
  have hp : (∫⁻ t in Ioo 0 c, H t) ≤ ENNReal.ofReal (c ^ 2) * (4 * E) := by
    have he := setLIntegral_Ioo_comp_sub_left H c 0 c
    simp only [sub_self, sub_zero] at he
    rw [← he]
    calc _ ≤ ∫⁻ t in Ioo 0 c, ENNReal.ofReal (c ^ 2) *
          ENNReal.ofReal (‖F (c + t) - F c‖ ^ 2 / t ^ 2) := by
           apply setLIntegral_mono' measurableSet_Ioo
           intro t ht
           have ho := hodd (c - t) ⟨by linarith [ht.2], by dsimp [c] at *; linarith [ht.1, pi_pos]⟩
           rw [show π - (c - t) = c + t by dsimp [c]; ring] at ho
           have hn : ‖F (c - t)‖ = ‖F (c + t)‖ := by rw [ho, norm_neg]
           dsimp only [H]
           rw [show cos (c - t) = sin t by dsimp [c]; exact cos_pi_div_two_sub t,
             hn, hz, sub_zero, ← ENNReal.ofReal_mul (sq_nonneg c)]
           apply ENNReal.ofReal_le_ofReal
           have hb := mul_le_mul_of_nonneg_left (inv_sin_sq_bound ht) (sq_nonneg ‖F (c + t)‖)
           dsimp [c] at *
           convert hb using 1 <;> ring
         _ = ENNReal.ofReal (c ^ 2) * ∫⁻ t in Ioo 0 c,
             ENNReal.ofReal (‖F (c + t) - F c‖ ^ 2 / t ^ 2) :=
           lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
         _ ≤ _ := by
           gcongr
           exact hright c ⟨by dsimp [c]; linarith [pi_pos], by dsimp [c]; linarith [pi_pos]⟩
             (by dsimp [c]; linarith [pi_pos])
  have hm : (∫⁻ t in Ioo (-c) 0, H t) ≤ ENNReal.ofReal (c ^ 2) * (4 * E) := by
    have he := setLIntegral_Ioo_comp_add_right H (-c) (-c) 0
    simp only [sub_self, zero_sub, neg_neg] at he
    rw [← he]
    calc _ ≤ ∫⁻ t in Ioo 0 c, ENNReal.ofReal (c ^ 2) *
          ENNReal.ofReal (‖F (-c + t) - F (-c)‖ ^ 2 / t ^ 2) := by
           apply setLIntegral_mono' measurableSet_Ioo
           intro t ht
           dsimp only [H]
           rw [show cos (t + -c) = sin t by
             dsimp [c]; simp [cos_add], show t + -c = -c + t by ring,
             show F (-c) = 0 from hzero, sub_zero,
             ← ENNReal.ofReal_mul (sq_nonneg c)]
           apply ENNReal.ofReal_le_ofReal
           have hb := mul_le_mul_of_nonneg_left (inv_sin_sq_bound ht) (sq_nonneg ‖F (-c + t)‖)
           dsimp [c] at *
           convert hb using 1 <;> ring
         _ = ENNReal.ofReal (c ^ 2) * ∫⁻ t in Ioo 0 c,
             ENNReal.ofReal (‖F (-c + t) - F (-c)‖ ^ 2 / t ^ 2) :=
           lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
         _ ≤ _ := by
           gcongr
           exact hright (-c) ⟨by dsimp [c]; linarith [pi_pos], by dsimp [c]; linarith [pi_pos]⟩
             (by dsimp [c]; linarith [pi_pos])
  have hsplit : (∫⁻ t in Ioo (-c) c, H t) ≤
      (∫⁻ t in Ioo (-c) 0, H t) + ∫⁻ t in Ioo 0 c, H t := by
    have hsub : Ioo (-c) c ⊆ Icc (-c) 0 ∪ Icc 0 c := by
      intro t ht
      rcases le_total t 0 with ht0 | ht0
      · exact Or.inl ⟨ht.1.le, ht0⟩
      · exact Or.inr ⟨ht0, ht.2.le⟩
    refine (lintegral_mono_set hsub).trans ((lintegral_union_le H _ _).trans_eq ?_)
    congr 1 <;> exact setLIntegral_congr Ioo_ae_eq_Icc.symm
  calc
    _ ≤ (∫⁻ t in Ioo (-c) 0, H t) + ∫⁻ t in Ioo 0 c, H t := hsplit
    _ ≤ ENNReal.ofReal (c ^ 2) * (4 * E) + ENNReal.ofReal (c ^ 2) * (4 * E) :=
      add_le_add hm hp
    _ = _ := by dsimp [E, c]; ring

private theorem continuous_odd_of_ae {F G : ℝ → ℂ} {J K : Set ℝ} {r : ℝ}
    (hJ : IsOpen J) (hK : MeasurableSet K) (hJK : J ⊆ K)
    (hm : MapsTo (fun t ↦ r - t) J J) (hc : ContinuousOn G K)
    (hGF : G =ᵐ[volume.restrict K] F) (ho : ∀ᵐ t, F (r - t) = -F t) :
    ∀ t ∈ J, G (r - t) = -G t := by
  have hg := (ae_restrict_iff' hK).1 hGF
  have hr := (Measure.measurePreserving_sub_left volume r).quasiMeasurePreserving.ae hg
  have hae : (fun t ↦ G (r - t)) =ᵐ[volume.restrict J] fun t ↦ -G t := by
    filter_upwards [ae_restrict_of_ae hg, ae_restrict_of_ae hr,
      ae_restrict_of_ae ho, ae_restrict_mem hJ.measurableSet] with t ht hrt hot htJ
    rw [hrt (hJK (hm htJ)), hot, ht (hJK htJ)]
  exact Measure.eqOn_open_of_ae_eq hae hJ
    ((hc.mono hJK).comp (continuousOn_const.sub continuousOn_id) hm) (hc.mono hJK).neg

/-- Odd reflection in the diagonal normal variable controls its cosine divisor.
    No pointwise values of the original representative on an edge are assumed. -/
theorem memLp_div_cos_snd_of_reflection {F D : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn (Ioo (-π / 2) (π / 2) ×ˢ Ioo (-2 * π) (2 * π)) 1 F D)
    (hF : MemLp F 2 (volume.restrict (Ioo (-π / 2) (π / 2) ×ˢ Ioo (-2 * π) (2 * π))))
    (hD : MemLp D 2 (volume.restrict (Ioo (-π / 2) (π / 2) ×ˢ Ioo (-2 * π) (2 * π))))
    (ho : ∀ᵐ p, F (p.1, π - p.2) = -F p)
    (hp : ∀ p, F (p.1, p.2 + 2 * π) = F p) :
    MemLp (fun p ↦ F p / (cos p.2 : ℂ)) 2
      (volume.restrict (Ioo (-π / 2) (π / 2) ×ˢ Ioo (-π / 2) (π / 2))) := by
  let I := Ioo (-π / 2) (π / 2)
  let J := Ioo (-2 * π) (2 * π)
  obtain ⟨G, hGm, hGF, hGa, hrows, -⟩ := hd.exists_l2_trace isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.mpr (by linarith [pi_pos])) (by linarith [pi_pos]) hF hD
  have hGFrows : ∀ᵐ a ∂volume.restrict I,
      (fun b ↦ G (a, b)) =ᵐ[volume.restrict J] fun b ↦ F (a, b) := by
    apply Measure.ae_ae_of_ae_prod (p := fun q ↦ G q = F q)
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hGF
  have ho' : ∀ᵐ p : ℝ × ℝ, F (p.1, -π - p.2) = -F p := by
    filter_upwards [ho] with p hpo
    have he := hp (p.1, -π - p.2)
    dsimp only [Prod.fst, Prod.snd] at he
    rw [show -π - p.2 + 2 * π = π - p.2 by ring] at he
    exact he.symm.trans hpo
  have hplus : ∀ᵐ a, ∀ᵐ b, F (a, π - b) = -F (a, b) := by
    apply Measure.ae_ae_of_ae_prod (p := fun q ↦ F (q.1, π - q.2) = -F q)
    simpa only [← Measure.volume_eq_prod] using ho
  have hminus : ∀ᵐ a, ∀ᵐ b, F (a, -π - b) = -F (a, b) := by
    apply Measure.ae_ae_of_ae_prod (p := fun q ↦ F (q.1, -π - q.2) = -F q)
    simpa only [← Measure.volume_eq_prod] using ho'
  have hbound : ∀ᵐ a ∂volume.restrict I,
      (∫⁻ b in I, ENNReal.ofReal (‖G (a, b)‖ ^ 2 / cos b ^ 2)) ≤
        (2 * (ENNReal.ofReal ((π / 2) ^ 2) * 4)) *
          ∫⁻ b in J, ENNReal.ofReal (‖D (a, b)‖ ^ 2) := by
    filter_upwards [hrows, hGFrows, ae_restrict_of_ae hplus, ae_restrict_of_ae hminus]
      with a ha hgf hop hom
    have hc : ContinuousOn (fun b ↦ G (a, b)) J :=
      continuousOn_Ioo_of_absolutelyContinuous ha.locally_absolutelyContinuous
    have hpos := continuous_odd_of_ae (J := Ioo (0 : ℝ) π) isOpen_Ioo measurableSet_Ioo
      (by intro t ht; exact ⟨by linarith [ht.1, pi_pos], by linarith [ht.2, pi_pos]⟩)
      (by intro t ht; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩) hc hgf hop
    have hneg := continuous_odd_of_ae (J := Ioo (-π) (0 : ℝ)) isOpen_Ioo measurableSet_Ioo
      (by intro t ht; exact ⟨by linarith [ht.1, pi_pos], by linarith [ht.2, pi_pos]⟩)
      (by intro t ht; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩) hc hgf hom
    have hz := hneg (-π / 2) ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
    rw [show -π - (-π / 2) = -π / 2 by ring] at hz
    exact interval_cos_hardy ha hpos (CharZero.eq_neg_self_iff.1 hz)
  have hfin : (∫⁻ p in I ×ˢ I, ENNReal.ofReal (‖G p‖ ^ 2 / cos p.2 ^ 2)) < ∞ := by
    have he : (∫⁻ p in I ×ˢ I, ENNReal.ofReal (‖G p‖ ^ 2 / cos p.2 ^ 2)) ≤
        (2 * (ENNReal.ofReal ((π / 2) ^ 2) * 4)) *
          ∫⁻ p in I ×ˢ J, ENNReal.ofReal (‖D p‖ ^ 2) := by
      rw [Measure.volume_eq_prod, setLIntegral_prod _ (by fun_prop)]
      rw [setLIntegral_prod _ (by
        rw [← Measure.volume_eq_prod]
        exact ENNReal.measurable_ofReal.comp_aemeasurable
          (hD.aestronglyMeasurable.aemeasurable.norm.pow_const 2))]
      rw [← lintegral_const_mul' _ _ (by finiteness)]
      exact lintegral_mono_ae hbound
    apply he.trans_lt
    apply ENNReal.mul_lt_top (by finiteness)
    exact hD.integrable_norm_pow (by norm_num) |>.lintegral_lt_top
  have hdiv : MemLp (fun p ↦ G p / (cos p.2 : ℂ)) 2 (volume.restrict (I ×ˢ I)) := by
    have mg : Measurable (fun p ↦ G p / (cos p.2 : ℂ)) := by fun_prop
    apply (memLp_two_iff_integrable_sq_norm mg.aestronglyMeasurable).2
    refine ⟨(mg.norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun p ↦ sq_nonneg _)]
    simpa only [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs] using hfin
  apply hdiv.ae_eq
  have hs : I ×ˢ I ⊆ I ×ˢ J := prod_mono subset_rfl (by
    intro t ht
    exact ⟨by dsimp [I, J] at *; linarith [ht.1, pi_pos],
      by dsimp [I, J] at *; linarith [ht.2, pi_pos]⟩)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hGF] with p hgp
  rw [hgp]

private theorem memLp_div_cos_fst_of_reflection {F D : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn (Ioo (-2 * π) (2 * π) ×ˢ Ioo (-π / 2) (π / 2)) 0 F D)
    (hF : MemLp F 2 (volume.restrict (Ioo (-2 * π) (2 * π) ×ˢ Ioo (-π / 2) (π / 2))))
    (hD : MemLp D 2 (volume.restrict (Ioo (-2 * π) (2 * π) ×ˢ Ioo (-π / 2) (π / 2))))
    (ho : ∀ᵐ p, F (π - p.1, p.2) = -F p)
    (hp : ∀ p, F (p.1 + 2 * π, p.2) = F p) :
    MemLp (fun p ↦ F p / (cos p.1 : ℂ)) 2
      (volume.restrict (Ioo (-π / 2) (π / 2) ×ˢ Ioo (-π / 2) (π / 2))) := by
  have hm : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
    rw [Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap
  have hs : Prod.swap ⁻¹' (Ioo (-2 * π) (2 * π) ×ˢ Ioo (-π / 2) (π / 2)) =
      Ioo (-π / 2) (π / 2) ×ˢ Ioo (-2 * π) (2 * π) := by ext p; simp [and_comm]
  have hsmall : Prod.swap ⁻¹' (Ioo (-π / 2) (π / 2) ×ˢ Ioo (-π / 2) (π / 2)) =
      Ioo (-π / 2) (π / 2) ×ˢ Ioo (-π / 2) (π / 2) := by ext p; simp [and_comm]
  have hds := hd.comp_swap_fst (isOpen_Ioo.prod isOpen_Ioo)
  rw [hs] at hds
  have hFs := hF.comp_measurePreserving
    (hm.restrict_preimage (measurableSet_Ioo.prod measurableSet_Ioo))
  have hDs := hD.comp_measurePreserving
    (hm.restrict_preimage (measurableSet_Ioo.prod measurableSet_Ioo))
  rw [hs] at hFs hDs
  have hos : ∀ᵐ p, (F ∘ Prod.swap) (p.1, π - p.2) = -(F ∘ Prod.swap) p :=
    hm.quasiMeasurePreserving.ae ho
  have hps : ∀ p : ℝ × ℝ, (F ∘ Prod.swap) (p.1, p.2 + 2 * π) = (F ∘ Prod.swap) p :=
    fun p ↦ hp p.swap
  have hdiv := memLp_div_cos_snd_of_reflection hds hFs hDs hos hps
  have hback := hdiv.comp_measurePreserving (hm.restrict_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo))
  rw [hsmall] at hback
  exact hback

private theorem memLp_of_comp_diagInv {U : Set (ℝ × ℝ)} (hU : MeasurableSet U)
    {F : ℝ × ℝ → ℂ} (hf : MemLp (F ∘ diagInv) 2 (volume.restrict (diagInv ⁻¹' U))) :
    MemLp F 2 (volume.restrict U) := by
  have h := diagInv.toHomeomorph.measurableEmbedding.memLp_map_measure_iff.2 hf
  change MemLp F 2 (Measure.map diagInv (volume.restrict (diagInv ⁻¹' U))) at h
  rw [← Measure.restrict_map diagInv.continuous.measurable hU, map_diagInv_volume,
    Measure.restrict_smul] at h
  have ht := h.smul_measure (c := ENNReal.ofReal (2 : ℝ)) (by finiteness)
  rw [smul_smul, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at ht
  norm_num at ht
  exact ht

private theorem ae_diagInv {P : ℝ × ℝ → Prop} (h : ∀ᵐ p, P p) :
    ∀ᵐ q, P (diagInv q) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  exact (Measure.LinearMap.quasiMeasurePreserving volume
    (diagInvLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) (by rw [det_diagInvLinear]; norm_num)).ae h

private theorem even_stream_diagonal_gradients {v : L2} (hs : InSector true true v) :
    MemLp (fun p ↦ (streamLiftX v p + streamLiftY v p) /
      (cos (diagCoord p).1 : ℂ)) 2 (volume.restrict cellSquare) ∧
    MemLp (fun p ↦ (streamLiftX v p - streamLiftY v p) /
      (cos (diagCoord p).2 : ℂ)) 2 (volume.restrict cellSquare) := by
  let I := Ioo (-π / 2) (π / 2)
  let J := Ioo (-2 * π) (2 * π)
  let U := diagRect J J
  let X := streamLiftX v
  let Y := streamLiftY v
  let H := fun i j ↦ liftL2 (streamSecondPartial i j v)
  have hpre : diagInv ⁻¹' U = J ×ˢ J := by ext q; exact mem_diagRect_diagInv
  have hU : IsOpen U := isOpen_diagRect isOpen_Ioo isOpen_Ioo
  have hb : Bornology.IsBounded U :=
    isBounded_diagRect (Metric.isBounded_Ioo _ _) (Metric.isBounded_Ioo _ _)
  have ml (g : L2) : MemLp (liftL2 g ∘ diagInv) 2 (volume.restrict (J ×ˢ J)) := by
    have hh := memLp_comp_diagInv hU.measurableSet (memLp_liftL2 g hb)
    rw [hpre] at hh
    exact hh
  have hw (i j : Fin 2) : HasWeakPartialOn univ i
      (liftL2 (streamPartial j v)) (H i j) :=
    hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial_streamSecondPartial v i j) univ
  let F := fun q ↦ X (diagInv q) + Y (diagInv q)
  let G := fun q ↦ X (diagInv q) - Y (diagInv q)
  let Da := fun q ↦ H 0 0 (diagInv q) + H 0 1 (diagInv q) +
    (H 1 0 (diagInv q) + H 1 1 (diagInv q))
  let Db := fun q ↦ (H 0 0 (diagInv q) - H 0 1 (diagInv q)) -
    (H 1 0 (diagInv q) - H 1 1 (diagInv q))
  have hda : HasWeakPartialOn univ 0 F Da := by
    simpa only [preimage_univ, Function.comp_def, F, Da, X, Y, streamLiftX, streamLiftY] using!
      HasWeakPartialOn.comp_diagInv_fst isOpen_univ ((hw 0 0).add (hw 0 1))
        ((hw 1 0).add (hw 1 1))
  have hdb : HasWeakPartialOn univ 1 G Db := by
    have hd (i) : HasWeakPartialOn univ i (fun p ↦ X p - Y p)
        (fun p ↦ H i 0 p - H i 1 p) := by
      simpa only [neg_one_mul, sub_eq_add_neg, X, Y, streamLiftX, streamLiftY] using!
        (hw i 0).add ((hw i 1).const_mul (-1))
    simpa only [preimage_univ, Function.comp_def, G, Db] using!
      HasWeakPartialOn.comp_diagInv_snd isOpen_univ (hd 0) (hd 1)
  have mF : MemLp F 2 (volume.restrict (J ×ˢ J)) := (ml _).add (ml _)
  have mG : MemLp G 2 (volume.restrict (J ×ˢ J)) := (ml _).sub (ml _)
  have mDa : MemLp Da 2 (volume.restrict (J ×ˢ J)) :=
    ((ml _).add (ml _)).add ((ml _).add (ml _))
  have mDb : MemLp Db 2 (volume.restrict (J ×ˢ J)) :=
    ((ml _).sub (ml _)).sub ((ml _).sub (ml _))
  have hIJ : I ⊆ J := by
    intro t ht
    exact ⟨by dsimp [I, J] at *; linarith [ht.1, pi_pos],
      by dsimp [I, J] at *; linarith [ht.2, pi_pos]⟩
  have lift {T : Torus → Torus} {hT : MeasurePreserving T} {g h : L2}
      (heq : pullback T hT g = h) {M : ℝ × ℝ → ℝ × ℝ}
      (hM : ∀ p, torusProj (M p) = T (torusProj p)) :
      ∀ᵐ p, liftL2 g (M p) = liftL2 h p := by
    filter_upwards [ae_torusProj (ae_comp_of_pullback_eq heq)] with p hp
    simpa only [liftL2, hM] using hp
  obtain ⟨h1x, h1y⟩ := hs.reflect₁_streamPartial
  obtain ⟨h2x, h2y⟩ := hs.reflect₂_streamPartial
  simp only [paritySign, ite_true, neg_smul, one_smul] at h1x h1y h2x h2y
  have e1 (p : ℝ × ℝ) : torusProj (π - p.2, π - p.1) = S₁ (torusProj p) := by
    simp [torusProj, S₁]
  have e2 (p : ℝ × ℝ) : torusProj (p.2 + π, p.1 + π) = S₂ (torusProj p) := by
    simp [torusProj, S₂, add_comm]
  have hneg (g : L2) : ∀ᵐ p, liftL2 (-g) p = -liftL2 g p := ae_torusProj (Lp.coeFn_neg g)
  have hrefl (g : L2) (a b : ℝ) :
      liftL2 g ((diagInv (a, b)).2 + π, (diagInv (a, b)).1 + π) =
        liftL2 g (diagInv (a, π - b)) := by
    have hh := (isPeriodicLift_liftL2 g (diagInv (a, π - b))).2
    rw [← hh]
    simp only [diagInv_apply]
    congr 1
    ext <;> ring
  have hFa : ∀ᵐ q, F (π - q.1, q.2) = -F q := by
    filter_upwards [ae_diagInv (lift h1x e1), ae_diagInv (lift h1y e1),
      ae_diagInv (hneg (streamPartial 0 v)), ae_diagInv (hneg (streamPartial 1 v))]
      with q hx hy nx ny
    have he : diagInv (π - q.1, q.2) = (π - (diagInv q).2, π - (diagInv q).1) := by
      simp only [diagInv_apply]; ext <;> ring
    simp only [F, X, Y, streamLiftX, streamLiftY, he, hx, hy, nx, ny]
    ring
  have hGb : ∀ᵐ q, G (q.1, π - q.2) = -G q := by
    filter_upwards [ae_diagInv (lift h2x e2), ae_diagInv (lift h2y e2)] with q hx hy
    rw [hrefl] at hx hy
    simp only [G, X, Y, streamLiftX, streamLiftY, hx, hy]
    ring
  have per (g : L2) (a b : ℝ) :
      liftL2 g (diagInv (a + 2 * π, b)) = liftL2 g (diagInv (a, b)) ∧
      liftL2 g (diagInv (a, b + 2 * π)) = liftL2 g (diagInv (a, b)) := by
    simp only [liftL2, torusProj, diagInv_apply]
    constructor
    · rw [show a + 2 * π + b = (a + b) + 2 * π by ring,
        show a + 2 * π - b = (a - b) + 2 * π by ring]
      simp only [Angle.coe_add, Angle.coe_two_pi, add_zero]
    · rw [show a + (b + 2 * π) = (a + b) + 2 * π by ring,
        show a - (b + 2 * π) = (a - b) - 2 * π by ring]
      simp only [Angle.coe_add, Angle.coe_sub, Angle.coe_two_pi, add_zero, sub_zero]
  have hFp : ∀ q, F (q.1 + 2 * π, q.2) = F q := by
    intro q
    exact congrArg₂ (· + ·) (per (streamPartial 0 v) q.1 q.2).1
      (per (streamPartial 1 v) q.1 q.2).1
  have hGp : ∀ q, G (q.1, q.2 + 2 * π) = G q := by
    intro q
    exact congrArg₂ (· - ·) (per (streamPartial 0 v) q.1 q.2).2
      (per (streamPartial 1 v) q.1 q.2).2
  have ma := memLp_div_cos_fst_of_reflection
    (hda.mono (subset_univ _))
    (mF.mono_measure (Measure.restrict_mono (prod_mono subset_rfl hIJ) le_rfl))
    (mDa.mono_measure (Measure.restrict_mono (prod_mono subset_rfl hIJ) le_rfl)) hFa hFp
  have mb := memLp_div_cos_snd_of_reflection
    (hdb.mono (subset_univ _))
    (mG.mono_measure (Measure.restrict_mono (prod_mono hIJ subset_rfl) le_rfl))
    (mDb.mono_measure (Measure.restrict_mono (prod_mono hIJ subset_rfl) le_rfl)) hGb hGp
  have hc : diagInv ⁻¹' cellSquare = I ×ˢ I := by
    ext q
    change (|(diagCoord (diagInv q)).1| < π / 2 ∧
      |(diagCoord (diagInv q)).2| < π / 2) ↔ q ∈ I ×ˢ I
    rw [diagCoord_diagInv]
    simp [I, abs_lt, neg_div]
  constructor
  · apply memLp_of_comp_diagInv isOpen_cellSquare.measurableSet
    simpa only [hc, Function.comp_def, diagCoord_diagInv, F, X, Y, I] using! ma
  · apply memLp_of_comp_diagInv isOpen_cellSquare.measurableSet
    simpa only [hc, Function.comp_def, diagCoord_diagInv, G, X, Y, I] using! mb

/-- The two diagonal derivatives of even H² data can be divided by their edge cosines. -/
theorem even_h2_diagonal_gradient_division {u dx dy : L2} (hu : MemSobolev 2 u)
    (hs : InSector true true u) (hx : HasFourierPartial 0 u dx)
    (hy : HasFourierPartial 1 u dy) :
    MemLp (fun p ↦ (liftL2 dx p + liftL2 dy p) / (cos (diagCoord p).1 : ℂ)) 2
      (volume.restrict cellSquare) ∧
    MemLp (fun p ↦ (liftL2 dx p - liftL2 dy p) / (cos (diagCoord p).2 : ℂ)) 2
      (volume.restrict cellSquare) := by
  obtain ⟨v, hv⟩ := hu.exists_hasFourierLaplacian
  have he (j : Fin 2) (d : L2) (hd : HasFourierPartial j u d) :
      d = streamPartial j v := by
    apply fourierCoeff_ext
    intro k
    rw [hd k, hasFourierPartial_streamPartial v j k]
    by_cases hk : k = 0
    · subst k
      simp [frequencyComponent]
    · have hc : fourierCoeff (invLap v) k = fourierCoeff u k := by
        have hn : (normSq k : ℂ) ≠ 0 := by exact_mod_cast (normSq_pos k hk).ne'
        simp only [fourierCoeff_invLap, hk, ite_false, hv k]
        field_simp
      rw [hc]
  rw [he 0 dx hx, he 1 dy hy]
  exact even_stream_diagonal_gradients (hs.even_laplacian hv)

end NoEmbeddedEigenvalues
