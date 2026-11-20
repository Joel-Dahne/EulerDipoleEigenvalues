import NoEmbeddedEigenvalues.RectangleH1Gluing
import NoEmbeddedEigenvalues.ReflectedTraces
import NoEmbeddedEigenvalues.TraceH2
import NoEmbeddedEigenvalues.SobolevApproximation
import NoEmbeddedEigenvalues.Analysis.AxisReflectionJets

/-!
# Smooth approximation with zero trace on one side of a square

Extend across the four sides by reflection, imposing the odd character only
on the zero-trace side. Approximate on an interior patch and project the
smooth functions onto that character.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open Set MeasureTheory Filter
open scoped Topology ContDiff

private theorem rectangle_trace_exists {l r a b t : ℝ} {f : ℝ × ℝ → ℂ}
    (hlr : l < r) (hab : a < b) (ht : t ∈ Icc a b)
    (hf : MemSobolevOn 1 (Ioo l r ×ˢ Ioo a b) f) :
    ∃ T, HasTransverseH1Trace l r a b t id f T := by
  obtain ⟨D, hd, hD⟩ := hf.2 1
  obtain ⟨G, hm, he, ha, _, _⟩ :=
    hd.exists_l2_trace isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.2 hlr) hab hf.1 hD
  exact ⟨aclTrace a b G D t, hlr, hab, ht, G, D, hm, he, hf.1.ae_eq he.symm, hD, ha,
    EventuallyEq.rfl⟩

/-- Extend to the left of the lower normal endpoint by a constant reflection
character. The only compatibility condition is equality of the two traces. -/
private theorem rectangle_reflect_lower {l r a b : ℝ} {f : ℝ × ℝ → ℂ} {T : ℝ → ℂ}
    {χ : ℂ}
    (hf : MemSobolevOn 1 (Ioo l r ×ˢ Ioo a b) f)
    (ht : HasTransverseH1Trace l r a b a id f T) (hc : ∀ s, χ * T s = T s) :
    MemSobolevOn 1 (Ioo l r ×ˢ Ioo (2 * a - b) b)
      (fun q ↦ if q.2 < a then χ * f (normalReflection (2 * a) q) else f q) := by
  let F := fun q : ℝ × ℝ ↦ if q.2 < a then χ * f (normalReflection (2 * a) q) else f q
  have hR := ht.reflect_normal (c := 2 * a) hf χ
  rw [show 2 * a - a = a by ring] at hR
  have heL : EqOn (fun q ↦ χ * f (normalReflection (2 * a) q)) F
      (Ioo l r ×ˢ Ioo (2 * a - b) a) := by
    intro q hq
    simp [F, hq.2.2]
  have heR : EqOn f F (Ioo l r ×ˢ Ioo a b) := by
    intro q hq
    simp [F, (not_lt_of_gt hq.2.1)]
  have heL' := (ae_restrict_mem (μ := volume)
    (measurableSet_Ioo.prod measurableSet_Ioo)).mono heL
  have heR' := (ae_restrict_mem (μ := volume)
    (measurableSet_Ioo.prod measurableSet_Ioo)).mono heR
  have htL := hR.2.congr_ae_pullback (C' := id) (F' := F) heL'
  rw [funext hc] at htL
  let hm : ∀ s t : ℝ, MeasurableSet (Ioo l r ×ˢ Ioo s t) :=
    fun _ _ ↦ measurableSet_Ioo.prod measurableSet_Ioo
  exact ((hR.1.congr_ae_on (hm _ _) ((ae_restrict_iff' (hm _ _)).1 heL')).glue_matching_trace
    (hf.congr_ae_on (hm _ _) ((ae_restrict_iff' (hm _ _)).1 heR')) htL
    (ht.congr_ae_pullback (C' := id) (F' := F) heR')).1

/-- Even reflection across the upper normal endpoint. -/
private theorem rectangle_reflect_upper {l r a b : ℝ} {f : ℝ × ℝ → ℂ}
    (hlr : l < r) (hab : a < b) (hf : MemSobolevOn 1 (Ioo l r ×ˢ Ioo a b) f) :
    MemSobolevOn 1 (Ioo l r ×ˢ Ioo a (2 * b - a))
      (fun q ↦ if b < q.2 then f (normalReflection (2 * b) q) else f q) := by
  obtain ⟨T, ht⟩ := rectangle_trace_exists hlr hab (right_mem_Icc.mpr hab.le) hf
  let F := fun q : ℝ × ℝ ↦ if b < q.2 then f (normalReflection (2 * b) q) else f q
  have hR := ht.reflect_normal (c := 2 * b) hf 1
  rw [show 2 * b - b = b by ring] at hR
  simp only [one_mul, id_eq] at hR
  have heL : EqOn f F (Ioo l r ×ˢ Ioo a b) := by
    intro q hq
    simp [F, (not_lt_of_gt hq.2.2)]
  have heR : EqOn (fun q ↦ f (normalReflection (2 * b) q)) F
      (Ioo l r ×ˢ Ioo b (2 * b - a)) := by
    intro q hq
    simp [F, hq.2.1]
  have heL' := (ae_restrict_mem (μ := volume)
    (measurableSet_Ioo.prod measurableSet_Ioo)).mono heL
  have heR' := (ae_restrict_mem (μ := volume)
    (measurableSet_Ioo.prod measurableSet_Ioo)).mono heR
  let hm : ∀ s t : ℝ, MeasurableSet (Ioo l r ×ˢ Ioo s t) :=
    fun _ _ ↦ measurableSet_Ioo.prod measurableSet_Ioo
  exact ((hf.congr_ae_on (hm _ _) ((ae_restrict_iff' (hm _ _)).1 heL')).glue_matching_trace
    (hR.1.congr_ae_on (hm _ _) ((ae_restrict_iff' (hm _ _)).1 heR'))
    (ht.congr_ae_pullback (C' := id) (F' := F) heL')
    (hR.2.congr_ae_pullback (C' := id) (F' := F) heR')).1

private theorem rectangle_swap_preimage (l r a b : ℝ) :
    Prod.swap ⁻¹' (Ioo l r ×ˢ Ioo a b) = Ioo a b ×ˢ Ioo l r := by
  ext q
  exact and_comm

private theorem rectangle_h1_swap {l r a b : ℝ} {f : ℝ × ℝ → ℂ}
    (hf : MemSobolevOn 1 (Ioo l r ×ˢ Ioo a b) f) :
    MemSobolevOn 1 (Ioo a b ×ˢ Ioo l r) (f ∘ Prod.swap) := by
  have ho : IsOpen (Ioo l r ×ˢ Ioo a b) := isOpen_Ioo.prod isOpen_Ioo
  refine ⟨by simpa only [rectangle_swap_preimage] using memLp_comp_swap ho.measurableSet hf.1,
    fun j ↦ ?_⟩
  obtain ⟨D, hd, hD⟩ := hf.2 (1 - j)
  refine ⟨D ∘ Prod.swap, ?_, ?_⟩
  · have h := hd.comp_swap ho
    rw [rectangle_swap_preimage, show 1 - (1 - j) = j by fin_cases j <;> decide] at h
    exact h
  · change MemLp _ 2 (volume.restrict _)
    simpa only [rectangle_swap_preimage] using memLp_comp_swap ho.measurableSet hD

/-- Two even normal reflections extend H¹ across both endpoints, without
changing the function on the original rectangle. -/
private theorem rectangle_extend_normal {l r a b : ℝ} {f : ℝ × ℝ → ℂ}
    (hlr : l < r) (hab : a < b) (hf : MemSobolevOn 1 (Ioo l r ×ˢ Ioo a b) f) :
    ∃ F, MemSobolevOn 1 (Ioo l r ×ˢ Ioo (3 * a - 2 * b) (2 * b - a)) F ∧
      EqOn F f (Ioo l r ×ˢ Ioo a b) := by
  let f₁ := fun q : ℝ × ℝ ↦ if b < q.2 then f (normalReflection (2 * b) q) else f q
  have h₁ : MemSobolevOn 1 (Ioo l r ×ˢ Ioo a (2 * b - a)) f₁ :=
    rectangle_reflect_upper hlr hab hf
  have hab' : a < 2 * b - a := by linarith
  obtain ⟨T, ht⟩ := rectangle_trace_exists hlr hab' (left_mem_Icc.mpr hab'.le) h₁
  have h₂ := rectangle_reflect_lower h₁ ht (χ := 1) (fun _ ↦ one_mul _)
  rw [show 2 * a - (2 * b - a) = 3 * a - 2 * b by ring] at h₂
  refine ⟨_, h₂, ?_⟩
  intro p hp
  simp [not_lt_of_gt hp.2.1, f₁, not_lt_of_gt hp.2.2]

/-- Extend off the closure of the half-square with the odd reflection on
the original symmetric strip. The value on the joining line is zero. -/
private theorem square_odd_extension {L : ℝ} {f : ℝ × ℝ → ℂ} (hL : 0 < L)
    (hf : MemSobolevOn 1 (Ioo 0 L ×ˢ Ioo 0 L) f)
    (ht : HasTransverseH1Trace 0 L 0 L 0 id f (fun _ ↦ 0)) :
    ∃ F, MemSobolevOn 1 (Ioo (-2 * L) (2 * L) ×ˢ Ioo (-5 * L) (3 * L)) F ∧
      EqOn F f (Ioo 0 L ×ˢ Ioo 0 L) ∧
      ∀ q ∈ Ioo 0 L ×ˢ Ioo (-L) L, F (axisReflect 1 q) = -F q := by
  let f₁ := fun q : ℝ × ℝ ↦ if q.2 < 0 then -f (q.1, -q.2) else f q
  have h₁ := rectangle_reflect_lower hf ht (χ := -1) (fun _ ↦ mul_zero _)
  have h₁' : MemSobolevOn 1 (Ioo 0 L ×ˢ Ioo (-L) L) f₁ := by
    simpa only [mul_zero, zero_sub, normalReflection_apply, neg_one_mul, f₁] using h₁
  let f₂ := fun q : ℝ × ℝ ↦ if q.2 = 0 then 0 else f₁ q
  have hn : ∀ᵐ q : ℝ × ℝ, q.2 ≠ 0 := by
    have h : ∀ᵐ t : ℝ, t ≠ 0 := by
      simp only [ae_iff, not_not, ofPred_eq_eq_singleton, measure_singleton]
    exact Measure.quasiMeasurePreserving_snd.ae h
  have h₂ : MemSobolevOn 1 (Ioo 0 L ×ˢ Ioo (-L) L) f₂ :=
    h₁'.congr_ae (hn.mono fun q hq ↦ by simp [f₂, hq])
  have hnL : -L < L := by linarith
  obtain ⟨f₃, h₃, e₃⟩ := rectangle_extend_normal hL hnL h₂
  obtain ⟨g, hg, eg⟩ := rectangle_extend_normal (by linarith : -5 * L < 3 * L) hL
    (rectangle_h1_swap (show MemSobolevOn 1 (Ioo 0 L ×ˢ Ioo (-5 * L) (3 * L)) f₃ by
      convert h₃ using 3 <;> ring))
  refine ⟨g ∘ Prod.swap, ?_, ?_, ?_⟩
  · convert rectangle_h1_swap hg using 3 <;> ring
  · intro q hq
    have hq' : q ∈ Ioo 0 L ×ˢ Ioo (-L) L := ⟨hq.1, by
      exact ⟨by linarith [hq.2.1], hq.2.2⟩⟩
    have hswap : q.swap ∈ Ioo (-5 * L) (3 * L) ×ˢ Ioo 0 L := by
      exact ⟨⟨show -5 * L < q.2 by linarith [hq.2.1],
        show q.2 < 3 * L by linarith [hq.2.2]⟩, hq.1⟩
    have eq : (g ∘ Prod.swap) q = f₂ q := (eg hswap).trans (e₃ hq')
    rw [eq]
    simp [f₂, f₁, hq.2.1.ne', not_lt_of_gt hq.2.1]
  · intro q hq
    have eq (p : ℝ × ℝ) (hp : p ∈ Ioo 0 L ×ˢ Ioo (-L) L) :
        (g ∘ Prod.swap) p = f₂ p :=
      (eg ⟨⟨show -5 * L < p.2 by linarith [hp.2.1],
        show p.2 < 3 * L by linarith [hp.2.2]⟩, hp.1⟩).trans (e₃ hp)
    change (g ∘ Prod.swap) (q.1, -q.2) = -(g ∘ Prod.swap) q
    rw [eq q hq, eq (q.1, -q.2) ⟨hq.1, ⟨by linarith [hq.2.2], by linarith [hq.2.1]⟩⟩]
    rcases lt_trichotomy q.2 0 with hy | hy | hy
    · simp [f₂, f₁, hy, hy.ne, neg_ne_zero.mpr hy.ne, not_lt_of_gt (neg_pos.mpr hy)]
    · simp [f₂, hy]
    · simp [f₂, f₁, not_lt_of_gt hy, hy.ne', neg_lt_zero.mpr hy, neg_ne_zero.mpr hy.ne']

private def oddProject (u : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  (1 / 2 : ℂ) * (u q - u (axisReflect 1 q))

private theorem oddProject_contDiff {u : ℝ × ℝ → ℂ} {n : WithTop ℕ∞}
    (hu : ContDiff ℝ n u) : ContDiff ℝ n (oddProject u) := by
  have hr : ContDiff ℝ n (axisReflect 1) :=
    contDiff_fst.prodMk contDiff_snd.neg
  exact contDiff_const.mul (hu.sub (hu.comp hr))

private theorem coordPartial_oddProject {u : ℝ × ℝ → ℂ}
    (hu : Differentiable ℝ u) (j : Fin 2) (q : ℝ × ℝ) :
    coordPartial j (oddProject u) q =
      (1 / 2 : ℂ) * (coordPartial j u q -
        (-1 : ℂ) ^ ([j] : List (Fin 2)).count 1 * coordPartial j u (axisReflect 1 q)) := by
  let r := axisReflect (1 : Fin 2)
  have hr : Differentiable ℝ r := (differentiable_fst.prodMk differentiable_snd.neg)
  have hg := coordPartial_comp_planeAffine hu (axisReflectionLinear 1) 0 j q
  rw [planeAffine_axisReflectionLinear] at hg
  have hg' : coordPartial j (u ∘ r) q =
      (-1 : ℂ) ^ ([j] : List (Fin 2)).count 1 * coordPartial j u (r q) := by
    rw [hg]
    fin_cases j <;> simp [affineCoeff, axisCoord, planeDirection, axisReflect, r]
  have hs : coordPartial j (oddProject u) q =
      (1 / 2 : ℂ) * (coordPartial j u q - coordPartial j (u ∘ r) q) := by
    unfold coordPartial
    split_ifs <;> simp only [partialX, partialY, oddProject, Function.comp_apply]
    · have h₀ := differentiable_id.prodMk (differentiable_const (𝕜 := ℝ) (E := ℝ) q.2)
      have h₁ := (hu.comp h₀).differentiableAt (x := q.1)
      have h₂ := ((hu.comp hr).comp h₀).differentiableAt (x := q.1)
      exact ((h₁.hasDerivAt.sub h₂.hasDerivAt).const_smul (1 / 2 : ℂ)).deriv
    · have h₀ := (differentiable_const (𝕜 := ℝ) (E := ℝ) q.1).prodMk differentiable_id
      have h₁ := (hu.comp h₀).differentiableAt (x := q.2)
      have h₂ := ((hu.comp hr).comp h₀).differentiableAt (x := q.2)
      exact ((h₁.hasDerivAt.sub h₂.hasDerivAt).const_smul (1 / 2 : ℂ)).deriv
  rw [hs, hg']

private theorem projected_jet_tendsto {L : ℝ} {f : ℝ × ℝ → ℂ}
    {D : List (Fin 2) → ℝ × ℝ → ℂ} {v : ℕ → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn 1 (Ioo 0 L ×ˢ Ioo (-L) L) f D)
    (hLp : ∀ w, w.length ≤ 1 → MemLp (D w) 2 (volume.restrict (Ioo 0 L ×ˢ Ioo (-L) L)))
    (hodd : ∀ q ∈ Ioo 0 L ×ˢ Ioo (-L) L, f (axisReflect 1 q) = -f q)
    (hv : ∀ n, Differentiable ℝ (v n))
    (hvL : ∀ w, w.length ≤ 1 → ∀ n,
      MemLp (classicalComplexJet w (v n)) 2 (volume.restrict (Ioo 0 L ×ˢ Ioo (-L) L)))
    (hl : ∀ w, w.length ≤ 1 → Tendsto (fun n ↦
      eLpNorm (fun q ↦ classicalComplexJet w (v n) q - D w q) 2
        (volume.restrict (Ioo 0 L ×ˢ Ioo (-L) L))) atTop (𝓝 0))
    (w : List (Fin 2)) (hw : w.length ≤ 1) :
    Tendsto (fun n ↦ eLpNorm (fun q ↦ classicalComplexJet w (oddProject (v n)) q - D w q)
      2 (volume.restrict (Ioo 0 L ×ˢ Ioo (-L) L))) atTop (𝓝 0) := by
  let V := Ioo (0 : ℝ) L ×ˢ Ioo (-L) L
  let μ := volume.restrict V
  have hVo : IsOpen V := isOpen_Ioo.prod isOpen_Ioo
  have hpre : axisReflect 1 ⁻¹' V = V := by
    ext p
    change (p.1, -p.2) ∈ V ↔ p ∈ V
    simp only [V, mem_prod, mem_Ioo]
    exact and_congr_right fun _ ↦ ⟨fun h ↦ ⟨by linarith [h.2], by linarith [h.1]⟩,
      fun h ↦ ⟨by linarith [h.2], by linarith [h.1]⟩⟩
  have hm : MeasurePreserving (axisReflect 1) μ μ := by
    have h := (measurePreserving_axisReflect 1).restrict_preimage hVo.measurableSet
    rwa [hpre] at h
  let c : ℂ := (-1 : ℂ) ^ w.count 1
  have hc : ‖c‖ = 1 := by simp [c]
  have hp := hD.axisReflect_entries hVo 1 hpre (c := -1)
    ((ae_restrict_mem hVo.measurableSet).mono fun q hq ↦ by simpa using hodd q hq) w hw
  have hj (n : ℕ) (q : ℝ × ℝ) :
      classicalComplexJet w (oddProject (v n)) q =
        (1 / 2 : ℂ) * (classicalComplexJet w (v n) q -
          c * classicalComplexJet w (v n) (axisReflect 1 q)) := by
    rcases w with _ | ⟨j, _ | ⟨i, w⟩⟩
    · simp [classicalComplexJet, oddProject, c]
    · exact coordPartial_oddProject (hv n) j q
    · simp at hw
  let e (n : ℕ) : ℝ × ℝ → ℂ := fun q ↦ classicalComplexJet w (v n) q - D w q
  have he (n : ℕ) : MemLp (e n) 2 μ := (hvL w hw n).sub (hLp w hw)
  have hn (n : ℕ) :
      eLpNorm (fun q ↦ classicalComplexJet w (oddProject (v n)) q - D w q) 2 μ ≤
        eLpNorm (e n) 2 μ + eLpNorm (e n) 2 μ := by
    have eq : (fun q ↦ classicalComplexJet w (oddProject (v n)) q - D w q) =ᵐ[μ]
        (1 / 2 : ℂ) • (e n - c • (e n ∘ axisReflect 1)) := by
      filter_upwards [hp] with q hq
      simp only [hj, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Function.comp_apply]
      dsimp [e]
      change c * D w (axisReflect 1 q) = (-1 : ℂ) * D w q at hq
      simp only [mul_sub, hq]
      ring
    rw [eLpNorm_congr_ae eq, eLpNorm_const_smul]
    have hhalf : ‖(1 / 2 : ℂ)‖ₑ ≤ 1 := by
      rw [← ofReal_norm]
      norm_num [norm_div]
    apply (mul_le_of_le_one_left' hhalf).trans
    refine (eLpNorm_sub_le (by norm_num)).trans_eq ?_
    have hc' : ‖c‖ₑ = 1 := by rw [← ofReal_norm, hc]; simp
    rw [eLpNorm_const_smul, hc', one_mul,
      eLpNorm_comp_measurePreserving (he n).aestronglyMeasurable hm]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun _ ↦ bot_le) hn
  change Tendsto _ atTop (𝓝 (0 : ENNReal))
  simpa only [zero_add] using (hl w hw).add (hl w hw)

/-- Smooth odd approximation on a square, with the two specified weak
partials. Only the chosen lower side is required to have zero trace. -/
theorem square_smooth_approximation_odd_snd {L : ℝ} {f dx dy : ℝ × ℝ → ℂ}
    (hL : 0 < L) (hf : MemSobolevOn 1 (Ioo 0 L ×ˢ Ioo 0 L) f)
    (hx : HasWeakPartialOn (Ioo 0 L ×ˢ Ioo 0 L) 0 f dx)
    (hy : HasWeakPartialOn (Ioo 0 L ×ˢ Ioo 0 L) 1 f dy)
    (ht : HasTransverseH1Trace 0 L 0 L 0 id f (fun _ ↦ 0)) :
    ∃ v : ℕ → ℝ × ℝ → ℂ, (∀ n, ContDiff ℝ 2 (v n)) ∧ (∀ n t, v n (t, 0) = 0) ∧
      Tendsto (fun n ↦ eLpNorm (fun q ↦ v n q - f q) 2
        (volume.restrict (Ioo 0 L ×ˢ Ioo 0 L))) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (fun q ↦ partialX (v n) q - dx q) 2
        (volume.restrict (Ioo 0 L ×ˢ Ioo 0 L))) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (fun q ↦ partialY (v n) q - dy q) 2
        (volume.restrict (Ioo 0 L ×ˢ Ioo 0 L))) atTop (𝓝 0) := by
  obtain ⟨F, hF, eF, hodd⟩ := square_odd_extension hL hf ht
  let Q := Ioo (0 : ℝ) L ×ˢ Ioo (0 : ℝ) L
  let V := Ioo (0 : ℝ) L ×ˢ Ioo (-L) L
  let U := Ioo (-2 * L) (2 * L) ×ˢ Ioo (-5 * L) (3 * L)
  have hVo : IsOpen V := isOpen_Ioo.prod isOpen_Ioo
  have hQV : Q ⊆ V := prod_mono Subset.rfl (Ioo_subset_Ioo (by linarith) le_rfl)
  have hcl : closure V = Icc (0 : ℝ) L ×ˢ Icc (-L) L := by
    dsimp [V]
    rw [closure_prod_eq, closure_Ioo hL.ne, closure_Ioo (show -L < L by linarith).ne]
  have hsub : closure V ⊆ U := by
    rw [hcl]
    intro p hp
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
      ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
  obtain ⟨D, hD, hDL, v, hv, hlim⟩ := local_smooth_approximation 1
    (show IsOpen U from isOpen_Ioo.prod isOpen_Ioo) hVo
    (hcl ▸ (show IsCompact (Icc (0 : ℝ) L ×ˢ Icc (-L) L) from isCompact_Icc.prod isCompact_Icc))
    hsub hF.memSobolevLocOn
  have ho : IsOpen Q := isOpen_Ioo.prod isOpen_Ioo
  have he : ∀ᵐ q, q ∈ Q → F q = f q := Eventually.of_forall eF
  have hpart (j : Fin 2) {d : ℝ × ℝ → ℂ} (hd : HasWeakPartialOn Q j f d) :
      D [j] =ᵐ[volume.restrict Q] d := by
    have h := (hD.2 [] (by simp) j).mono hQV
    rw [hD.1] at h
    exact (ae_restrict_iff' ho.measurableSet).mpr
      ((h.congr_ae_on ho.measurableSet he (Eventually.of_forall fun _ _ ↦ rfl)).ae_eq ho hd)
  have hp (w : List (Fin 2)) (hw : w.length ≤ 1) {d : ℝ × ℝ → ℂ}
      (heq : D w =ᵐ[volume.restrict Q] d) :
      Tendsto (fun n ↦ eLpNorm (fun q ↦ classicalComplexJet w (oddProject (v n)) q - d q)
        2 (volume.restrict Q)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (projected_jet_tendsto hD hDL hodd (fun n ↦ (hv n).1.differentiable (by simp))
        (fun w hw ↦ (hlim w hw).1) (fun w hw ↦ (hlim w hw).2) w hw) (fun _ ↦ bot_le)
    intro n
    change eLpNorm (fun q ↦ classicalComplexJet w (oddProject (v n)) q - d q) 2
      (volume.restrict Q) ≤ _
    rw [eLpNorm_congr_ae (heq.mono fun q hq ↦
      congrArg (fun z : ℂ ↦ classicalComplexJet w (oddProject (v n)) q - z) hq.symm)]
    exact eLpNorm_mono_measure _ (Measure.restrict_mono hQV le_rfl)
  refine ⟨fun n ↦ oddProject (v n), fun n ↦ oddProject_contDiff ((hv n).1.of_le (by simp)),
    fun n t ↦ by simp [oddProject, axisReflect], ?_, ?_, ?_⟩
  · exact hp [] (by simp) (by rw [hD.1]; exact (ae_restrict_iff' ho.measurableSet).mpr he)
  · exact hp [0] (by simp) (hpart 0 hx)
  · exact hp [1] (by simp) (hpart 1 hy)

/-- The same density result with the first coordinate as the odd normal. -/
theorem square_smooth_approximation_odd_fst {L : ℝ} {f dx dy : ℝ × ℝ → ℂ}
    (hL : 0 < L) (hf : MemSobolevOn 1 (Ioo 0 L ×ˢ Ioo 0 L) f)
    (hx : HasWeakPartialOn (Ioo 0 L ×ˢ Ioo 0 L) 0 f dx)
    (hy : HasWeakPartialOn (Ioo 0 L ×ˢ Ioo 0 L) 1 f dy)
    (ht : HasTransverseH1Trace 0 L 0 L 0 Prod.swap f (fun _ ↦ 0)) :
    ∃ v : ℕ → ℝ × ℝ → ℂ, (∀ n, ContDiff ℝ 2 (v n)) ∧ (∀ n t, v n (0, t) = 0) ∧
      Tendsto (fun n ↦ eLpNorm (fun q ↦ v n q - f q) 2
        (volume.restrict (Ioo 0 L ×ˢ Ioo 0 L))) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (fun q ↦ partialX (v n) q - dx q) 2
        (volume.restrict (Ioo 0 L ×ˢ Ioo 0 L))) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (fun q ↦ partialY (v n) q - dy q) 2
        (volume.restrict (Ioo 0 L ×ˢ Ioo 0 L))) atTop (𝓝 0) := by
  let Q := Ioo (0 : ℝ) L ×ˢ Ioo (0 : ℝ) L
  let μ := volume.restrict Q
  have hQ : IsOpen Q := isOpen_Ioo.prod isOpen_Ioo
  have hpre : Prod.swap ⁻¹' Q = Q := rectangle_swap_preimage _ _ _ _
  have hx' : HasWeakPartialOn Q 1 (f ∘ Prod.swap) (dx ∘ Prod.swap) := by
    simpa only [hpre] using hx.comp_swap_fst hQ
  have hy' : HasWeakPartialOn Q 0 (f ∘ Prod.swap) (dy ∘ Prod.swap) := by
    simpa only [hpre, sub_self] using hy.comp_swap hQ
  obtain ⟨v, hv, hzero, tv, tx, ty⟩ :=
    square_smooth_approximation_odd_snd hL (rectangle_h1_swap hf) hy' hx'
      (show HasTransverseH1Trace 0 L 0 L 0 id (f ∘ Prod.swap) (fun _ ↦ 0) from ht)
  have hm : MeasurePreserving Prod.swap μ μ := by
    have h : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
      simpa only [Measure.volume_eq_prod] using
        (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume))
    have h' := h.restrict_preimage hQ.measurableSet
    rwa [hpre] at h'
  have he (g : ℝ × ℝ → ℂ) : eLpNorm (g ∘ Prod.swap) 2 μ = eLpNorm g 2 μ := by
    have h := (Homeomorph.prodComm ℝ ℝ).measurableEmbedding.eLpNorm_map_measure
      (g := g) (p := 2) (μ := μ)
    exact (hm.map_eq ▸ h).symm
  have hs {g d : ℝ × ℝ → ℂ} :
      (fun q ↦ g (q.swap) - d q) =
        (fun q ↦ g q - d q.swap) ∘ Prod.swap := by
    funext q
    simp only [Function.comp_apply, Prod.swap_swap]
  have hX (g : ℝ × ℝ → ℂ) : partialX (g ∘ Prod.swap) = partialY g ∘ Prod.swap := rfl
  have hY (g : ℝ × ℝ → ℂ) : partialY (g ∘ Prod.swap) = partialX g ∘ Prod.swap := rfl
  have hlim {g : ℕ → ℝ × ℝ → ℂ} {d : ℝ × ℝ → ℂ}
      (h : Tendsto (fun n ↦ eLpNorm (fun q ↦ g n q - d q.swap) 2 μ) atTop (𝓝 0)) :
      Tendsto (fun n ↦ eLpNorm (fun q ↦ (g n ∘ Prod.swap) q - d q) 2 μ) atTop (𝓝 0) := by
    refine h.congr' (Eventually.of_forall fun n ↦ ?_)
    change eLpNorm (fun q ↦ g n q - d q.swap) 2 μ =
      eLpNorm (fun q ↦ g n q.swap - d q) 2 μ
    rw [hs, he]
  refine ⟨fun n ↦ v n ∘ Prod.swap, fun n ↦ (hv n).comp (contDiff_snd.prodMk contDiff_fst),
    hzero, hlim tv, ?_, ?_⟩
  · simpa only [hX] using hlim ty
  · simpa only [hY] using hlim tx

private theorem eLpNorm_two_rpow_eq_ofReal_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℂ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ ^ (2 : ℝ) = ENNReal.ofReal (∫ q, ‖f q‖ ^ 2 ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
    (Eventually.of_forall fun _ ↦ sq_nonneg _)]
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num)
    hf.aestronglyMeasurable
  have h' : eLpNorm f 2 μ ^ (2 : ℝ) = ∫⁻ q, ‖f q‖ₑ ^ (2 : ℝ) ∂μ := by
    simpa only [NNReal.coe_ofNat, ENNReal.coe_ofNat] using h
  refine h'.trans (lintegral_congr fun q ↦ ?_)
  rw [← ofReal_norm, show (2 : ℝ) = (↑(2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
    ENNReal.ofReal_pow (norm_nonneg _)]

private theorem tendsto_integral_sq_of_eLpNorm {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℂ} (hf : ∀ n, MemLp (f n) 2 μ)
    (ht : Tendsto (fun n ↦ eLpNorm (f n) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ q, ‖f n q‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n ↦ eLpNorm (f n) 2 μ ^ (2 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
      using (ENNReal.continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp ht
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsq
  simp only [ENNReal.toReal_zero, Function.comp_def] at h
  refine h.congr' (Eventually.of_forall fun n ↦ ?_)
  rw [eLpNorm_two_rpow_eq_ofReal_integral (hf n),
    ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ sq_nonneg _)]

/-- On a fixed rectangle the classical values of smooth H¹ approximants at the
top converge to the canonical trace. The estimate is applied to the difference,
using its actual weak normal derivative. -/
theorem HasTransverseH1Trace.tendsto_smooth_top {l r a b : ℝ}
    {f d : ℝ × ℝ → ℂ} {T : ℝ → ℂ} {v : ℕ → ℝ × ℝ → ℂ}
    (ht : HasTransverseH1Trace l r a b b id f T)
    (hd : HasWeakPartialOn (Ioo l r ×ˢ Ioo a b) 1 f d)
    (hF : MemLp f 2 (volume.restrict (Ioo l r ×ˢ Ioo a b)))
    (hdL : MemLp d 2 (volume.restrict (Ioo l r ×ˢ Ioo a b)))
    (hv : ∀ n, ContDiff ℝ 1 (v n))
    (tv : Tendsto (fun n ↦ eLpNorm (fun q ↦ v n q - f q) 2
      (volume.restrict (Ioo l r ×ˢ Ioo a b))) atTop (𝓝 0))
    (td : Tendsto (fun n ↦ eLpNorm (fun q ↦ partialY (v n) q - d q) 2
      (volume.restrict (Ioo l r ×ˢ Ioo a b))) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun s ↦ v n (s, b) - T s) 2
      (volume.restrict (Ioo l r))) atTop (𝓝 0) := by
  let R := Ioo l r ×ˢ Ioo a b
  let μ := volume.restrict R
  let σ := volume.restrict (Ioo l r)
  let W (n : ℕ) (q : ℝ × ℝ) := v n q - f q
  let E (n : ℕ) (q : ℝ × ℝ) := partialY (v n) q - d q
  let B (n : ℕ) (s : ℝ) := v n (s, b) - T s
  have hab := ht.2.1
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  have hr : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hc : IsCompact (closure R) := by
    dsimp [R]
    rw [closure_prod_eq, closure_Ioo ht.1.ne, closure_Ioo hab.ne]
    exact isCompact_Icc.prod isCompact_Icc
  have hWL (n : ℕ) : MemLp (W n) 2 μ :=
    (memLp_two_restrict_of_continuous (hv n).continuous hr hc).sub hF
  have hEL (n : ℕ) : MemLp (E n) 2 μ :=
    (memLp_two_restrict_of_continuous ((contDiff_partialY (n := 0) (hv n)).continuous)
      hr hc).sub hdL
  have hWeak (n : ℕ) : HasWeakPartialOn R 1 (W n) (E n) := by
    simpa only [W, E, coordPartial, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
      neg_one_mul, sub_eq_add_neg] using
      (hasWeakPartialOn_of_contDiff (hv n) R 1).add (hd.const_mul (-1))
  have hbound (n : ℕ) :
      MemLp (B n) 2 σ ∧
      (∫ s, ‖B n s‖ ^ 2 ∂σ) ≤ (2 / (b - a)) * (∫ q, ‖W n q‖ ^ 2 ∂μ) +
        2 * (b - a) * ∫ q, ‖E n q‖ ^ 2 ∂μ := by
    obtain ⟨G, hGm, hGW, hG, _, hGt⟩ := (hWeak n).exists_l2_trace isOpen_Ioo
      ordConnected_Ioo (nonempty_Ioo.2 ht.1) hab (hWL n) (hEL n)
    obtain ⟨_, _, _, H, D, _, hHF, hH, hD, hHD, hT⟩ := ht
    have hGL := (hWL n).ae_eq hGW.symm
    have he : G =ᵐ[μ] fun q ↦ v n q - H q := by
      filter_upwards [hGW, hHF] with q h₁ h₂
      change H q = f q at h₂
      exact h₁.trans (congrArg (v n q - ·) h₂.symm)
    have hC : ∀ᵐ s ∂σ, ContinuousOn (fun y ↦ v n (s, y) - H (s, y)) (Ioo a b) :=
      (hHD.ae_continuousOn isOpen_Ioo).mono fun s hs ↦
        ((hv n).continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.sub hs
    have hBT : B n =ᵐ[σ] aclTrace a b G (E n) b := by
      have : (𝓝[Ioo a b] b).NeBot := right_nhdsWithin_Ioo_neBot hab
      filter_upwards [hT, hG.ae_tendsto_trace hab hGL (hEL n),
        hHD.ae_tendsto_trace hab hH hD,
        ae_eqOn_sections_of_ae_eq isOpen_Ioo he (hG.ae_continuousOn isOpen_Ioo) hC]
        with s hs hGs hHs heq
      have hvb : ContinuousWithinAt (fun y ↦ v n (s, y)) (Ioo a b) b :=
        ((hv n).continuous.comp
          (continuous_const.prodMk continuous_id)).continuousAt.continuousWithinAt
      have hl := hvb.tendsto.sub (hHs b hb)
      have hmem : ∀ᶠ y in 𝓝[Ioo a b] b, y ∈ Ioo a b := self_mem_nhdsWithin
      have hevent : ∀ᶠ y in 𝓝[Ioo a b] b, v n (s, y) - H (s, y) = G (s, y) :=
        hmem.mono fun y hy ↦ (heq y hy).symm
      change v n (s, b) - T s = _
      rw [hs]
      exact tendsto_nhds_unique (hl.congr' hevent) (hGs b hb)
    have h := hGt b hb
    exact ⟨h.1.ae_eq hBT.symm, (integral_congr_ae (hBT.mono fun s hs ↦ by rw [hs])).le.trans h.2⟩
  have hW := (tendsto_integral_sq_of_eLpNorm hWL tv).const_mul (2 / (b - a))
  have hE := (tendsto_integral_sq_of_eLpNorm hEL td).const_mul (2 * (b - a))
  have hB : Tendsto (fun n ↦ ∫ s, ‖B n s‖ ^ 2 ∂σ) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _) (fun n ↦ (hbound n).2)
    simpa only [mul_zero, zero_add] using hW.add hE
  have hsq : Tendsto (fun n ↦ eLpNorm (B n) 2 σ ^ (2 : ℝ)) atTop (𝓝 0) := by
    simpa only [eLpNorm_two_rpow_eq_ofReal_integral (hbound _).1, ENNReal.ofReal_zero]
      using ENNReal.tendsto_ofReal hB
  have hs := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    ENNReal.rpow_one, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hs

end NoEmbeddedEigenvalues
