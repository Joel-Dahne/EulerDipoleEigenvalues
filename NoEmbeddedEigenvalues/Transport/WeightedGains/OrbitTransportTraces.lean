module

public import NoEmbeddedEigenvalues.Transport.ResonantVanishing
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.TraceL2

/-!
# Local L² endpoint traces of weak transport

Normalize flow time by the orbit period. The quarter endpoints become the
fixed angular sections ±1/8. A level cutoff allows the angular weak-derivative
bridge on the whole cell; rectangle trace bounds and uniqueness identify its
traces with every continuous orbitwise representative.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ENNReal

private theorem ae_eq_of_unit_periodic {α : Type*} {F G : ℝ → α}
    (hF : Function.Periodic F 1) (hG : Function.Periodic G 1)
    (heq : F =ᵐ[volume.restrict (Ico (-1 / 4 : ℝ) (3 / 4))] G) : F =ᵐ[volume] G := by
  have hglobal := (ae_restrict_iff' measurableSet_Ico).1 heq
  have hshift (n : ℤ) : ∀ᵐ t : ℝ, t + n ∈ Ico (-1 / 4 : ℝ) (3 / 4) → F (t + n) = G (t + n) :=
    (measurePreserving_add_right volume (n : ℝ)).quasiMeasurePreserving.ae hglobal
  filter_upwards [ae_all_iff.2 hshift] with t ht
  let n : ℤ := -⌊t + 1 / 4⌋
  have hn : t + n ∈ Ico (-1 / 4 : ℝ) (3 / 4) := by
    have h0 := Int.floor_le (t + 1 / 4)
    have h1 := Int.lt_floor_add_one (t + 1 / 4)
    dsimp [n]
    push_cast
    constructor <;> linarith
  have hf : F (t + n) = F t := by simpa only [mul_one] using hF.int_mul n t
  have hg : G (t + n) = G t := by simpa only [mul_one] using hG.int_mul n t
  simpa only [hf, hg] using ht n hn

/-- Planar a.e. equality on an orbit annulus transfers to a.e. full orbit,
including the entire real time lift, without evaluating an exceptional orbit. -/
theorem ae_orbit_congr {u v : ℝ × ℝ → ℂ} {h₀ : ℝ} (h₀1 : h₀ ≤ 1)
    (heq : u =ᵐ[volume.restrict (orbitAnnulus 0 h₀)] v) :
    ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)), ∀ᵐ t : ℝ,
      u (dipoleOrbit h t) = v (dipoleOrbit h t) := by
  let A := orbitAnnulus 0 h₀
  have hAm := measurableSet_orbitAnnulus 0 h₀
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null
    (s := {p | p ∈ A ∧ u p ≠ v p}) (μ := (volume : Measure (ℝ × ℝ))) (by
      have h := (ae_restrict_iff' hAm).1 heq
      rw [ae_iff] at h
      refine measure_mono_null ?_ h
      intro p hp hn
      exact hp.2 (hn hp.1))
  have hG : Measurable fun q : ℝ × ℝ ↦
      ENNReal.ofReal (2 * orbitPeriod q.1) * N.indicator 1 (actionAngleInv q) :=
    (ENNReal.measurable_ofReal.comp (((measurable_eighthPeriod.const_mul 8).const_mul 2).comp
      measurable_fst)).mul ((measurable_one.indicator hNm).comp measurable_actionAngleInv)
  have hc := lintegral_cellSquare_actionAngle (measurable_one.indicator hNm)
  have hz : ∫⁻ p in cellSquare, N.indicator (1 : ℝ × ℝ → ℝ≥0∞) p = 0 :=
    le_antisymm ((setLIntegral_le_lintegral _ _).trans (by
      rw [lintegral_indicator_one hNm, hN0])) bot_le
  rw [hz, eq_comm, lintegral_eq_zero_iff hG.lintegral_prod_right'] at hc
  have hsub : Ioo (0 : ℝ) h₀ ⊆ Ioo 0 1 := Ioo_subset_Ioo le_rfl h₀1
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hc,
    ae_restrict_mem measurableSet_Ioo] with h hh hI
  have h1 := hI.2.trans_le h₀1
  have hS := orbitPeriod_pos hI.1 h1
  have hθ := (lintegral_eq_zero_iff (hG.comp measurable_prodMk_left)).1 hh
  have he : (fun θ ↦ u (actionAngleInv (h, θ))) =ᵐ[volume.restrict (Ico (-1 / 4 : ℝ) (3 / 4))]
      (fun θ ↦ v (actionAngleInv (h, θ))) := by
    filter_upwards [hθ] with θ hθ
    have hw : ENNReal.ofReal (2 * orbitPeriod h) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.2 (by positivity))
    have hn : actionAngleInv (h, θ) ∉ N := by
      simpa only [Function.comp_apply, Pi.zero_apply, mul_eq_zero, hw, false_or,
        indicator_apply_eq_zero, Pi.one_apply, one_ne_zero, imp_false] using hθ
    by_contra hne
    exact hn (hNsub ⟨⟨actionAngleInv_mem_puncturedCell hI.1 h1 θ,
      by rw [levelCoord_actionAngleInv hI.1 h1]; exact hI⟩, hne⟩)
  have heall := ae_eq_of_unit_periodic
    (fun θ ↦ congrArg u (actionAngleInv_add_one hI.1 h1 θ))
    (fun θ ↦ congrArg v (actionAngleInv_add_one hI.1 h1 θ)) he
  have hq : QuasiMeasurePreserving (fun t : ℝ ↦ t / orbitPeriod h) volume volume := by
    simpa only [smul_eq_mul, div_eq_inv_mul] using
      Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (inv_ne_zero hS.ne')
  filter_upwards [hq.ae heall] with t ht
  simpa only [actionAngleInv, div_mul_cancel₀ t hS.ne'] using ht

/-- The countable annulus exhaustion also permits a zero lower level cutoff. -/
theorem ae_orbit_restriction_zero {U : Set (ℝ × ℝ)} {u k : ℝ × ℝ → ℂ}
    {h₀ : ℝ} (h₀1 : h₀ < 1) (hA : orbitAnnulus 0 h₀ ⊆ U)
    (hd : HasWeakL0On U u k) :
    ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)), ∃ Z : ℝ → ℂ,
      (∀ᵐ t, Z t = u (dipoleOrbit h t)) ∧ Function.Periodic Z (orbitPeriod h) ∧
      (∀ c d, AbsolutelyContinuousOnInterval Z c d) ∧
      ∀ᵐ t, HasDerivAt Z (k (dipoleOrbit h t)) t := by
  let P := fun h ↦ ∃ Z : ℝ → ℂ,
    (∀ᵐ t, Z t = u (dipoleOrbit h t)) ∧ Function.Periodic Z (orbitPeriod h) ∧
    (∀ c d, AbsolutelyContinuousOnInterval Z c d) ∧
    ∀ᵐ t, HasDerivAt Z (k (dipoleOrbit h t)) t
  have hq (a b : ℚ) : ∀ᵐ h : ℝ, 0 < (a : ℝ) → (a : ℝ) < b → (b : ℝ) < h₀ →
      h ∈ Ioo (a : ℝ) b → P h := by
    by_cases ha : 0 < (a : ℝ)
    · by_cases hab : (a : ℝ) < b
      · by_cases hb : (b : ℝ) < h₀
        · have hAu : orbitAnnulus a b ⊆ U := fun p hp ↦ hA
            ⟨hp.1, ⟨ha.trans hp.2.1, hp.2.2.trans hb⟩⟩
          filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1
            (ae_orbit_restriction ha hab (hb.trans h₀1) hAu hd)] with h hh _ _ _ hmem
          exact hh hmem
        · exact ae_of_all _ fun _ _ _ hb' ↦ (hb hb').elim
      · exact ae_of_all _ fun _ _ hab' ↦ (hab hab').elim
    · exact ae_of_all _ fun _ ha' ↦ (ha ha').elim
  have hall := ae_all_iff.2 fun a ↦ ae_all_iff.2 fun b ↦ hq a b
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_Ioo] with h hh hhI
  obtain ⟨a, ha0, hah⟩ := exists_rat_btwn hhI.1
  obtain ⟨b, hhb, hbh⟩ := exists_rat_btwn hhI.2
  exact hh a b ha0 (hah.trans hhb) hbh ⟨hah, hhb⟩

/-- L² data pull back to genuine L² functions on compact level/angular bands. -/
theorem memLp_actionAngleInv_band {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {u : ℝ × ℝ → ℂ} (hu : MemLp u 2 (volume.restrict U))
    {a b h₀ : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < h₀) (h₀1 : h₀ < 1)
    (hA : orbitAnnulus 0 h₀ ⊆ U) :
    MemLp (u ∘ actionAngleInv) 2
      (volume.restrict (Ioo a b ×ˢ Ioo (-1 / 4 : ℝ) (3 / 4))) := by
  classical
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_Ioo (a := a / 2) (b := (b + h₀) / 2)) (isClosed_Icc (a := a) (b := b))
    (fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hχt : tsupport χ ⊆ Ioo 0 1 := by
    rw [tsupport, hχs, closure_Ioo (by linarith)]
    exact Icc_subset_Ioo (by linarith) (by linarith)
  have hui : MemLp (U.indicator u) 2 (volume.restrict cellSquare) :=
    ((memLp_indicator_iff_restrict hU.measurableSet.nullMeasurableSet).2 hu).mono_measure Measure.restrict_le_self
  have hm := memLp_cutoff_actionInput hχ hχt hui
  have hm' := hm.mono_measure
    (show volume.restrict (Ioo a b ×ˢ Ioo (-1 / 4 : ℝ) (3 / 4)) ≤
      (volume : Measure ℝ).prod (volume.restrict (Ico (-1 / 4 : ℝ) (3 / 4))) by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      exact Measure.prod_mono Measure.restrict_le_self
        (Measure.restrict_mono Ioo_subset_Ico_self le_rfl))
  apply hm'.ae_eq
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with q hq
  have h0 : 0 < q.1 := ha.trans hq.1.1
  have h1 : q.1 < 1 := hq.1.2.trans (hb.trans h₀1)
  have hpU : actionAngleInv q ∈ U := hA
    ⟨actionAngleInv_mem_puncturedCell h0 h1 q.2,
      by rw [levelCoord_actionAngleInv h0 h1]; exact ⟨h0, hq.1.2.trans hb⟩⟩
  simp only [Function.comp_apply, indicator_of_mem hpU,
    (hχ1 q.1).1 (Ioo_subset_Icc_self hq.1), Complex.ofReal_one, one_mul]

/-- On each compact level interval, quarter endpoint values have L²
representatives agreeing with every periodic ACL orbit representative. -/
theorem exists_l2_orbit_endpoints {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {u k : ℝ × ℝ → ℂ} (hu : MemLp u 2 (volume.restrict U))
    (hk : MemLp k 2 (volume.restrict U)) (hd : HasWeakL0On U u k)
    {a b h₀ : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < h₀) (h₀1 : h₀ < 1)
    (hA : orbitAnnulus 0 h₀ ⊆ U) :
    ∃ Em Ep : ℝ → ℂ,
      MemLp Em 2 (volume.restrict (Ioo a b)) ∧
      MemLp Ep 2 (volume.restrict (Ioo a b)) ∧
      ∀ᵐ h ∂(volume.restrict (Ioo a b)), ∀ Z : ℝ → ℂ,
        (∀ᵐ t, Z t = u (dipoleOrbit h t)) →
        (∀ c d, AbsolutelyContinuousOnInterval Z c d) →
        Z (-eighthPeriod h) = Em h ∧ Z (eighthPeriod h) = Ep h := by
  classical
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_Ioo (a := a / 2) (b := (b + h₀) / 2)) (isClosed_Icc (a := a) (b := b))
    (fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hχt : tsupport χ ⊆ Ioo 0 h₀ := by
    rw [tsupport, hχs, closure_Ioo (by linarith)]
    exact Icc_subset_Ioo (by linarith) (by linarith)
  let F : ℝ × ℝ → ℂ := fun q ↦ (χ (levelCoord (actionAngleInv q)) : ℂ) *
    u (actionAngleInv q)
  let D : ℝ × ℝ → ℂ := fun q ↦ (orbitPeriod q.1 : ℂ) *
    ((χ (levelCoord (actionAngleInv q)) : ℂ) * k (actionAngleInv q))
  let R : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo (-1 / 4 : ℝ) (3 / 4)
  have hcut (q : ℝ × ℝ) (hq : q ∈ R) :
      (χ (levelCoord (actionAngleInv q)) : ℂ) = 1 := by
    rw [levelCoord_actionAngleInv (ha.trans hq.1.1)
      (hq.1.2.trans (hb.trans h₀1)), (hχ1 q.1).1 (Ioo_subset_Icc_self hq.1)]
    rfl
  have hweak : HasWeakPartialOn R 1 F D :=
    ((hd.levelCutoff hA hχ hχt).comp_actionAngleInv).mono
      (prod_mono (Ioo_subset_Ioo ha.le (hb.trans h₀1).le) (subset_univ _))
  have hFL : MemLp F 2 (volume.restrict R) := by
    apply (memLp_actionAngleInv_band hU hu ha hab hb h₀1 hA).ae_eq
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with q hq
    simp only [F, hcut q hq, one_mul, Function.comp_apply]
  have hS : MemLp (fun q : ℝ × ℝ ↦ (orbitPeriod q.1 : ℂ)) ⊤ (volume.restrict R) := by
    have hc : ContinuousOn orbitPeriod (Icc a b) :=
      continuousOn_orbitPeriod.mono (Icc_subset_Ioo ha (hb.trans h₀1))
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    apply memLp_top_of_bound
      ((Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_orbitPeriod.comp (s := R) continuous_fst.continuousOn
          (fun q hq ↦ ⟨ha.trans hq.1.1, hq.1.2.trans (hb.trans h₀1)⟩))).aestronglyMeasurable
            (measurableSet_Ioo.prod measurableSet_Ioo)) C
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with q hq
    simpa only [Function.comp_apply, Complex.norm_real] using
      hC q.1 (Ioo_subset_Icc_self hq.1)
  have hDL : MemLp D 2 (volume.restrict R) := by
    apply (hS.mul (memLp_actionAngleInv_band hU hk ha hab hb h₀1 hA)).ae_eq
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with q hq
    simp only [D, hcut q hq, one_mul, Function.comp_apply, Pi.mul_apply]
  obtain ⟨G, hGm, hGF, hG, hGH, hT⟩ := hweak.exists_l2_trace
    isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.2 hab) (by norm_num) hFL hDL
  let Em := aclTrace (-1 / 4) (3 / 4) G D (-1 / 8)
  let Ep := aclTrace (-1 / 4) (3 / 4) G D (1 / 8)
  refine ⟨Em, Ep, (hT _ (by constructor <;> norm_num)).1,
    (hT _ (by constructor <;> norm_num)).1, ?_⟩
  have hGF' : ∀ᵐ h ∂(volume.restrict (Ioo a b)),
      ∀ᵐ θ ∂(volume.restrict (Ioo (-1 / 4 : ℝ) (3 / 4))),
        G (h, θ) = u (actionAngleInv (h, θ)) := by
    have heq : G =ᵐ[volume.restrict R] (u ∘ actionAngleInv) := by
      filter_upwards [hGF, ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)]
        with q hq hqR
      simpa only [F, hcut q hqR, one_mul, Function.comp_apply] using hq
    rw [show volume.restrict R = (volume.restrict (Ioo a b)).prod
      (volume.restrict (Ioo (-1 / 4 : ℝ) (3 / 4))) by
        rw [Measure.volume_eq_prod, Measure.prod_restrict]] at heq
    exact Measure.ae_ae_of_ae_prod heq
  filter_upwards [hGF', hGH, hG.ae_continuousOn isOpen_Ioo,
    ae_restrict_mem measurableSet_Ioo] with h heq hH hcont hh
  intro Z hZ hac
  have h0 : 0 < h := ha.trans hh.1
  have h1 : h < 1 := hh.2.trans (hb.trans h₀1)
  have hSpos := orbitPeriod_pos h0 h1
  have hq : QuasiMeasurePreserving (fun θ : ℝ ↦ θ * orbitPeriod h) volume volume := by
    simpa only [smul_eq_mul, mul_comm] using
      Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) hSpos.ne'
  have hcZ : Continuous Z := continuous_iff_continuousAt.2 fun t ↦
    ((hac (t - 1) (t + 1)).continuousOn.continuousAt (by
      rw [uIcc_of_le (by linarith)]; exact Icc_mem_nhds (by linarith) (by linarith)))
  have hz : (fun θ ↦ Z (θ * orbitPeriod h)) =ᵐ[volume.restrict (Ioo (-1 / 4 : ℝ) (3 / 4))]
      (fun θ ↦ G (h, θ)) := by
    filter_upwards [ae_restrict_of_ae (hq.ae hZ), heq] with θ hθ hGθ
    exact hθ.trans hGθ.symm
  have hwhole := Measure.eqOn_open_of_ae_eq hz isOpen_Ioo
    (hcZ.comp (continuous_id.mul continuous_const)).continuousOn
    hcont
  have htrace (θ : ℝ) (hθ : θ ∈ Ioo (-1 / 4 : ℝ) (3 / 4)) :
      Z (θ * orbitPeriod h) = aclTrace (-1 / 4) (3 / 4) G D θ h := by
    change Z (θ * orbitPeriod h) =
      intervalH1Extension (-1 / 4) (3 / 4) (fun t ↦ G (h, t)) (fun t ↦ D (h, t)) θ
    rw [hH.extension_eq (by norm_num) hθ]
    exact hwhole hθ
  constructor
  · have he : (-1 / 8 : ℝ) * orbitPeriod h = -eighthPeriod h := by
      unfold orbitPeriod; ring
    simpa only [he] using htrace (-1 / 8) (by constructor <;> norm_num)
  · have he : (1 / 8 : ℝ) * orbitPeriod h = eighthPeriod h := by
      unfold orbitPeriod; ring
    simpa only [he] using htrace (1 / 8) (by constructor <;> norm_num)

/-- One choice of orbitwise continuous representatives has locally L² endpoint
functions. Their measurability follows from agreement with rectangle traces. -/
theorem orbit_endpoint_functions {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {u k : ℝ × ℝ → ℂ} (hu : MemLp u 2 (volume.restrict U))
    (hk : MemLp k 2 (volume.restrict U)) (hd : HasWeakL0On U u k)
    {h₀ : ℝ} (h₀1 : h₀ < 1) (hA : orbitAnnulus 0 h₀ ⊆ U) :
    ∃ Em Ep : ℝ → ℂ,
      (∀ a b, 0 < a → a < b → b < h₀ →
        MemLp Em 2 (volume.restrict (Ioo a b)) ∧
        MemLp Ep 2 (volume.restrict (Ioo a b))) ∧
      ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)), ∃ Z : ℝ → ℂ,
        (∀ᵐ t, Z t = u (dipoleOrbit h t)) ∧ Function.Periodic Z (orbitPeriod h) ∧
        (∀ c d, AbsolutelyContinuousOnInterval Z c d) ∧
        (∀ᵐ t, HasDerivAt Z (k (dipoleOrbit h t)) t) ∧
        Z (-eighthPeriod h) = Em h ∧ Z (eighthPeriod h) = Ep h := by
  classical
  let P := fun h ↦ ∃ Z : ℝ → ℂ,
    (∀ᵐ t, Z t = u (dipoleOrbit h t)) ∧ Function.Periodic Z (orbitPeriod h) ∧
    (∀ c d, AbsolutelyContinuousOnInterval Z c d) ∧
    ∀ᵐ t, HasDerivAt Z (k (dipoleOrbit h t)) t
  let Z : ℝ → ℝ → ℂ := fun h ↦ if hp : P h then hp.choose else fun _ ↦ 0
  have hZ : ∀ᵐ h ∂(volume.restrict (Ioo 0 h₀)),
      (∀ᵐ t, Z h t = u (dipoleOrbit h t)) ∧ Function.Periodic (Z h) (orbitPeriod h) ∧
      (∀ c d, AbsolutelyContinuousOnInterval (Z h) c d) ∧
      ∀ᵐ t, HasDerivAt (Z h) (k (dipoleOrbit h t)) t := by
    filter_upwards [ae_orbit_restriction_zero h₀1 hA hd] with h hh
    change P h at hh
    simpa only [Z, dite_eq_left hh] using hh.choose_spec
  let Em : ℝ → ℂ := fun h ↦ Z h (-eighthPeriod h)
  let Ep : ℝ → ℂ := fun h ↦ Z h (eighthPeriod h)
  refine ⟨Em, Ep, ?_, hZ.mono fun h hh ↦ ⟨Z h, hh.1, hh.2.1, hh.2.2.1,
    hh.2.2.2, rfl, rfl⟩⟩
  intro a b ha hab hb
  obtain ⟨Tm, Tp, hTm, hTp, htrace⟩ := exists_l2_orbit_endpoints hU hu hk hd ha hab hb h₀1 hA
  have hZab := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo ha.le hb.le) hZ
  have he : (Em =ᵐ[volume.restrict (Ioo a b)] Tm) ∧
      (Ep =ᵐ[volume.restrict (Ioo a b)] Tp) := by
    constructor <;> filter_upwards [hZab, htrace] with h hh ht
    · exact (ht (Z h) hh.1 hh.2.2.1).1
    · exact (ht (Z h) hh.1 hh.2.2.1).2
  exact ⟨hTm.ae_eq he.1.symm, hTp.ae_eq he.2.symm⟩

end NoEmbeddedEigenvalues
