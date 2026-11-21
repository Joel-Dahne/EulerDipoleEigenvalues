module

public import NoEmbeddedEigenvalues.EvenEven.TraceExclusion.EigenfunctionTransport
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.TraceL2
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.LocalJets
public import NoEmbeddedEigenvalues.Transport.WeightedForcing.WeightedTransport
public import NoEmbeddedEigenvalues.Transport.WeightedGains.FirstTransportGain
public import NoEmbeddedEigenvalues.Transport.WeightedGains.SecondTransportGain
public import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.WeakPointRemoval
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.LocalContinuousRepresentative
public import NoEmbeddedEigenvalues.Analysis.Inequalities.IntervalLinearHardy
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.AxisReflectionJets
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.SpecifiedJetLp
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.TraceH2
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.LocalToGlobal
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.WeakJetOperations
public import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.ScaledInteriorEnergy
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.NormalAverage
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.DoubleDivision
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.SobolevApproximation

/-!
# Local analytic interfaces for the quotient construction

Weak derivative jets specify derivatives rather than differentiating arbitrary Sobolev
representatives. Radial integrability is stated separately from energies, so a default
Bochner integral cannot stand in for a divergent norm. The radius is Euclidean: the
usual metric on a product of real normed spaces uses the maximum norm.

All division identities and parity hypotheses are a.e. identities on their domains.
The derivative jets in point removal are only required on the punctured disk.
-/

@[expose] public section

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- One-coordinate H³ division, including the uniform H² bound (`lem:odd-h3-division`). -/
theorem odd_h3_division {l r b : ℝ} (hlr : l < r) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ),
      MemSobolevOn 3 (axisRectangle 1 b l r) R →
      HasWeakJetOn 3 (axisRectangle 1 b l r) R D →
      (∀ᵐ p ∂(volume.restrict (axisRectangle 1 b l r)), R (axisReflect 1 p) = -R p) →
      ∃ (V : ℝ × ℝ → ℂ) (E : List (Fin 2) → ℝ × ℝ → ℂ),
        MemSobolevOn 2 (axisRectangle 1 b l r) V ∧
        HasWeakJetOn 2 (axisRectangle 1 b l r) V E ∧
        (∀ᵐ p ∂(volume.restrict (axisRectangle 1 b l r)), R p = (p.2 : ℂ) * V p) ∧
        (∀ᵐ p ∂(volume.restrict (axisRectangle 1 b l r)), V (axisReflect 1 p) = V p) ∧
        weakJetEnergy 2 (axisRectangle 1 b l r) E ≤
          C * weakJetEnergy 3 (axisRectangle 1 b l r) D := by
  let U := Ioo l r ×ˢ Ioo (-b) b
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  let : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr
    ((measure_mono (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)).trans_lt
      ((isCompact_Icc.prod isCompact_Icc).measure_lt_top (μ := volume))).ne
  have hT (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : MapsTo (normalScale t) U U := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    change x ∈ Ioo l r ∧ -b < t * y ∧ t * y < b
    refine ⟨hx, ?_, ?_⟩
    · nlinarith only [mul_lt_mul_of_pos_left hy.1 ht.1, mul_pos hb (sub_pos.mpr ht.2)]
    · nlinarith only [mul_lt_mul_of_pos_left hy.2 ht.1, mul_pos hb (sub_pos.mpr ht.2)]
  refine ⟨4, by norm_num, fun R D hR hD hodd ↦ ?_⟩
  have hR₃ : MemSobolevOn 3 U R := hR
  have hD₃ : HasWeakJetOn 3 U R D := hD
  have hL (w : List (Fin 2)) (hw : w.length ≤ 3) := hR₃.memLp_weakJet hU hD₃ w hw
  let M (w : List (Fin 2)) : ℝ × ℝ → ℂ :=
    if hw : w.length ≤ 3 then (hL w hw).aestronglyMeasurable.mk (D w) else 0
  have hMm (w : List (Fin 2)) (hw : w.length ≤ 3) : Measurable (M w) := by
    simpa only [M, dite_eq_left hw] using
      (hL w hw).aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hMe (w : List (Fin 2)) (hw : w.length ≤ 3) : D w =ᵐ[volume.restrict U] M w := by
    simpa only [M, dite_eq_left hw] using (hL w hw).aestronglyMeasurable.ae_eq_mk
  have hML (w : List (Fin 2)) (hw : w.length ≤ 3) := (hL w hw).ae_eq (hMe w hw)
  have hmw (w : List (Fin 2)) (hw : w.length < 3) (j : Fin 2) :
      HasWeakPartialOn U j (M w) (M (j :: w)) :=
    (hD₃.2 w hw j).congr_ae_on hU.measurableSet
      ((ae_restrict_iff' hU.measurableSet).mp (hMe w hw.le))
      ((ae_restrict_iff' hU.measurableSet).mp (hMe (j :: w) (by simp; omega)))
  let E (w : List (Fin 2)) := normalAverage (w.count 1) (M (w ++ [1]))
  let V := E []
  have havg (w : List (Fin 2)) (hw : w.length ≤ 2) :
      MemLp (E w) 2 (volume.restrict U) ∧ squareEnergy U (E w) ≤
        4 * squareEnergy U (D (w ++ [1])) := by
    have hn : (w ++ [1]).length ≤ 3 := by simp; omega
    have he : squareEnergy U (D (w ++ [1])) = squareEnergy U (M (w ++ [1])) :=
      integral_congr_ae ((hMe _ hn).fun_comp fun z : ℂ ↦ ‖z‖ ^ 2)
    rw [he]
    exact normalAverage_memLp hU.measurableSet hT (hMm _ hn) (hML _ hn) _
  have hE : HasWeakJetOn 2 U V E := by
    refine ⟨rfl, fun w hw j ↦ ?_⟩
    have hn : (w ++ [1]).length < 3 := by simp; omega
    have hn' : (j :: (w ++ [1])).length ≤ 3 := by simp; omega
    have h := (hmw _ hn j).average_normal hU hT
      (hMm _ hn.le) (hMm _ hn') (hML _ hn.le) (hML _ hn') (w.count 1)
    have hc : (j :: w).count 1 = w.count 1 + if j = 0 then 0 else 1 := by
      fin_cases j
      · change (0 :: w).count 1 = w.count 1 + 0
        rw [List.count_cons_of_ne (by decide : (0 : Fin 2) ≠ 1), add_zero]
      · exact List.count_cons_self
    simpa only [E, hc, List.cons_append] using h
  have hder : HasWeakPartialOn U 1 R (M [1]) := by
    have h := (hD₃.2 [] (by decide) 1).congr_ae_on hU.measurableSet
      (Eventually.of_forall fun _ _ ↦ rfl)
      ((ae_restrict_iff' hU.measurableSet).mp (hMe [1] (by decide)))
    rwa [hD₃.1] at h
  have hbase : ∀ᵐ p ∂volume.restrict U, R p = (p.2 : ℂ) * V p :=
    hder.eq_mul_normalAverage_of_odd hb hlr hR₃.memLp (hML [1] (by decide))
      (hMm [1] (by decide)) hodd
  have hmaps : MapsTo (axisReflect 1) U U := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    change x ∈ Ioo l r ∧ -b < -y ∧ -y < b
    exact ⟨hx, neg_lt_neg hy.2, neg_lt.mp hy.1⟩
  have hbaseR := ((measurePreserving_axisReflect 1).quasiMeasurePreserving.restrict hmaps).ae hbase
  have hzero : ∀ᵐ p ∂volume.restrict U, p.2 ≠ 0 := by
    apply ae_restrict_of_ae
    rw [Measure.volume_eq_prod]
    have hh : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ 0 := by
      rw [ae_iff]
      simp
    exact Measure.quasiMeasurePreserving_snd.ae hh
  have heven : ∀ᵐ p ∂volume.restrict U, V (axisReflect 1 p) = V p := by
    filter_upwards [hbase, hbaseR, hodd, hzero] with p hp hr ho hn
    have h : (p.2 : ℂ) * V (axisReflect 1 p) = (p.2 : ℂ) * V p := by
      change R (axisReflect 1 p) = ((-p.2 : ℝ) : ℂ) * V (axisReflect 1 p) at hr
      rw [ho, hp, Complex.ofReal_neg, neg_mul, neg_inj] at hr
      exact hr.symm
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hn) h
  have hEn (k : ℕ) : 0 ≤ radialJetEnergy k 0 U 0 D :=
    Finset.sum_nonneg fun _ _ ↦ integral_nonneg fun _ ↦ sq_nonneg _
  have horder (k : ℕ) (hk : k ≤ 2) :
      radialJetEnergy k 0 U 0 E ≤ 4 * radialJetEnergy (k + 1) 0 U 0 D := by
    unfold radialJetEnergy
    simp only [pow_zero, div_one, Finset.mul_sum]
    let snoc (v : Fin k → Fin 2) : Fin (k + 1) → Fin 2 := Fin.snoc v 1
    refine Finset.sum_le_sum_of_injOn snoc (fun x _ y _ h ↦ ?_)
      (Finset.subset_univ _) (fun v _ ↦ ?_)
      (fun _ _ _ ↦ mul_nonneg (by norm_num) (integral_nonneg fun _ ↦ sq_nonneg _))
    · funext i
      have hh := congrFun h i.castSucc
      simpa only [snoc, Fin.snoc_castSucc] using hh
    · have hh : List.ofFn (snoc v) = List.ofFn v ++ [1] := by
        rw [List.ofFn_succ']
        simp only [snoc, Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]
      rw [hh]
      exact (havg (List.ofFn v) (List.length_ofFn.trans_le hk)).2
  have henergy : weakJetEnergy 2 U E ≤ 4 * weakJetEnergy 3 U D := by
    unfold weakJetEnergy
    rw [Finset.sum_range_succ' (fun k ↦ radialJetEnergy k 0 U 0 D) 3, mul_add,
      Finset.mul_sum]
    refine (Finset.sum_le_sum fun k hk ↦ horder k
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).trans ?_
    exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (hEn 0))
  exact ⟨V, E, memSobolevOn_iff_exists_weakJet.mpr ⟨E, hE, fun w hw ↦ (havg w hw).1⟩,
    hE, hbase, heven, henergy⟩

/-- A nonzero continuous value at the center would force the weighted squared
mass in a square of side `2 * r` to grow at least as fast as `r⁻²`. -/
private theorem eq_zero_of_memLp_div_radius_sq {ρ : ℝ} (hρ : 0 < ρ)
    {g : ℝ × ℝ → ℂ} (hg : ContinuousOn g (localDisk 0 ρ))
    (hw : MemLp (fun p ↦ g p / (localRadius 0 p ^ 2 : ℂ)) 2
      (volume.restrict (localDisk 0 ρ))) : g 0 = 0 := by
  by_contra hn
  let c := ‖g 0‖ / 2
  have hc : 0 < c := half_pos (norm_pos_iff.mpr hn)
  have ho := isOpen_localDisk 0 ρ
  have hz : (0 : ℝ × ℝ) ∈ localDisk 0 ρ := by simpa [localDisk, localRadius] using hρ
  have hlarge : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ), c < ‖g p‖ :=
    ((hg.continuousAt (ho.mem_nhds hz)).norm.tendsto.eventually
      (lt_mem_nhds (by dsimp [c]; linarith [norm_pos_iff.mpr hn])))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (ho.mem_nhds hz) hlarge)
  let W := fun p ↦ ‖g p / (localRadius 0 p ^ 2 : ℂ)‖ ^ 2
  have hW : IntegrableOn W (localDisk 0 ρ) := hw.integrable_norm_pow (by norm_num)
  let M := ∫ p in localDisk 0 ρ, W p
  have hbound (r : ℝ) (hr : 0 < r) (hrδ : r < δ) :
      c ^ 2 ≤ (2 * r) ^ 2 * M := by
    let B := Metric.ball (0 : ℝ × ℝ) r
    have hBδ : B ⊆ Metric.ball (0 : ℝ × ℝ) δ := Metric.ball_subset_ball hrδ.le
    have hB : B ⊆ localDisk 0 ρ := fun p hp ↦ (hball (hBδ hp)).1
    have hvol : volume B = ENNReal.ofReal (2 * r) * ENNReal.ofReal (2 * r) := by
      change volume (Metric.ball ((0 : ℝ), (0 : ℝ)) r) = _
      rw [← ball_prod_same, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_ball]
    have hfinite : volume B ≠ ⊤ := by rw [hvol]; finiteness
    have hne : ∀ᵐ p ∂(volume.restrict B), p ≠ (0 : ℝ × ℝ) :=
      ae_restrict_of_ae (by rw [ae_iff]; simp [Measure.volume_eq_prod])
    have hle : ∀ᵐ p ∂(volume.restrict B), c ^ 2 ≤ (2 * r) ^ 4 * W p := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet, hne] with p hp hpne
      have hrad : localRadius 0 p ≤ 2 * r :=
        (localRadius_le_two_dist 0 p).trans (by linarith [Metric.mem_ball.mp hp])
      have hp0 := localRadius_ne_zero hpne
      have he : ‖g p‖ ^ 2 = localRadius 0 p ^ 4 * W p := by
        dsimp [W]
        rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ localRadius 0 p from Real.sqrt_nonneg _)]
        field_simp
      calc
        c ^ 2 ≤ ‖g p‖ ^ 2 :=
          pow_le_pow_left₀ hc.le (hball (hBδ hp)).2.le 2
        _ = localRadius 0 p ^ 4 * W p := he
        _ ≤ (2 * r) ^ 4 * W p := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (Real.sqrt_nonneg _) hrad 4) (sq_nonneg _)
    have hi := integral_mono_ae (integrableOn_const (C := c ^ 2) hfinite)
      ((hW.mono_set hB).const_mul ((2 * r) ^ 4)) hle
    rw [integral_const, Measure.real, Measure.restrict_apply_univ, hvol, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * r), smul_eq_mul, integral_const_mul] at hi
    have hmono : (∫ p in B, W p) ≤ M := integral_mono_measure
      (Measure.restrict_mono hB le_rfl) (Eventually.of_forall fun p ↦ sq_nonneg _) hW
    apply le_of_mul_le_mul_left _ (show 0 < (2 * r) ^ 2 by positivity)
    calc
      _ = (2 * r * (2 * r)) * c ^ 2 := by ring
      _ ≤ (2 * r) ^ 4 * (∫ p in B, W p) := hi
      _ ≤ (2 * r) ^ 4 * M := mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = (2 * r) ^ 2 * ((2 * r) ^ 2 * M) := by ring
  have hlim : Tendsto (fun r : ℝ ↦ (2 * r) ^ 2 * M) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun r : ℝ ↦ (2 * r) ^ 2 * M) := by fun_prop
    have ht := (hcont.continuousWithinAt (s := Ioi 0) (x := 0)).tendsto
    simpa using ht
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r ∈ Ioo 0 δ := Ioo_mem_nhdsGT hδ
  exact (not_le_of_gt (sq_pos_of_pos hc)) (ge_of_tendsto hlim
    (hsmall.mono fun r hr ↦ hbound r hr.1 hr.2))

/-- Weighted removal of a point, with a genuine continuous representative
(`lem:weighted-h2-point-removal`). No assigned raw value at zero is used.
The specified jet and full-disk bounds already imply the local regularity
assumed on the punctured disk. -/
theorem weighted_h2_point_removal {ρ : ℝ} (hρ : 0 < ρ) {V : ℝ × ℝ → ℂ}
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (_hV : MemSobolevLocOn 2 (localDisk 0 ρ \ {0}) V)
    (hD : HasWeakJetOn 2 (localDisk 0 ρ \ {0}) V D)
    (h0 : RadialJetLp 0 2 (localDisk 0 ρ) 0 D)
    (h1 : RadialJetLp 1 1 (localDisk 0 ρ) 0 D)
    (h2 : RadialJetLp 2 0 (localDisk 0 ρ) 0 D) :
    MemSobolevOn 2 (localDisk 0 ρ) V ∧
      ∃ g : ℝ × ℝ → ℂ, ContinuousOn g (localDisk 0 ρ) ∧ g 0 = 0 ∧
        V =ᵐ[volume.restrict (localDisk 0 ρ)] g := by
  have hv : MemLp V 2 (volume.restrict (localDisk 0 ρ)) := by
    rw [← hD.1]
    exact memLp_of_div_localRadius_pow (h0 [] rfl)
  have hfirst (j : Fin 2) : MemLp (D [j]) 2 (volume.restrict (localDisk 0 ρ)) :=
    memLp_of_div_localRadius_pow (h1 [j] rfl)
  have hsecond (i j : Fin 2) : MemLp (D [i, j]) 2 (volume.restrict (localDisk 0 ρ)) := by
    simpa using h2 [i, j] rfl
  have hloc {F : ℝ × ℝ → ℂ} (hF : MemLp F 2 (volume.restrict (localDisk 0 ρ))) :
      LocallyIntegrableOn F (localDisk 0 ρ) :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hF.locallyIntegrable (by norm_num))
  have htwo : MemSobolevOn 2 (localDisk 0 ρ) V := by
    refine ⟨hv, fun j ↦ ⟨D [j], ?_, hfirst j, fun i ↦ ⟨D [i, j], ?_, hsecond i j⟩⟩⟩
    · have hd := hD.2 [] (by decide) j
      rw [hD.1] at hd
      exact hd.remove_point (hloc hv) (hloc (hfirst j))
    · exact (hD.2 [j] (by simp) i).remove_point (hloc (hfirst j)) (hloc (hsecond i j))
  obtain ⟨g, hg, he⟩ := exists_continuousOn_rep_of_memSobolevLocOn_two
    (isOpen_localDisk 0 ρ) htwo.memSobolevLocOn
  refine ⟨htwo, g, hg, eq_zero_of_memLp_div_radius_sq hρ hg ?_, he⟩
  apply (h0 [] rfl).ae_eq
  filter_upwards [he] with p hp
  rw [hD.1, hp]

/-- The continuous sections of an a.e. odd derivative vanish on the axis.
Apply interior Hardy on each section and integrate the resulting squared bound. -/
private theorem odd_vertical_hardy {a l r : ℝ} (ha : 0 < a) (hlr : l < r)
    {d dd : ℝ × ℝ → ℂ}
    (hd : MemLp d 2 (volume.restrict (Ioo l r ×ˢ Ioo (-a) a)))
    (hdd : MemLp dd 2 (volume.restrict (Ioo l r ×ˢ Ioo (-a) a)))
    (hw : HasWeakPartialOn (Ioo l r ×ˢ Ioo (-a) a) 1 d dd)
    (ho : ∀ᵐ p ∂(volume.restrict (Ioo l r ×ˢ Ioo (-a) a)), d (p.1, -p.2) = -d p) :
    MemLp (fun p ↦ d p / (p.2 : ℂ)) 2 (volume.restrict (Ioo l r ×ˢ Ioo (-a) a)) ∧
      (∫ p in Ioo l r ×ˢ Ioo (-a) a, ‖d p / (p.2 : ℂ)‖ ^ 2) ≤
        4 * ∫ p in Ioo l r ×ˢ Ioo (-a) a, ‖dd p‖ ^ 2 := by
  let I := Ioo l r
  let J := Ioo (-a) a
  let U := I ×ˢ J
  have hz : (0 : ℝ) ∈ J := ⟨neg_lt_zero.mpr ha, ha⟩
  have hneg : MapsTo (fun t : ℝ ↦ -t) J J := fun t ht ↦
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hmaps : MapsTo (axisReflect 1) U U :=
    fun p hp ↦ ⟨hp.1, hneg hp.2⟩
  obtain ⟨G, hGm, hGe, hGa⟩ := hw.exists_acl_sections isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.mpr hlr) isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.mpr (hz.1.trans hz.2))
  have hGr := ((measurePreserving_axisReflect 1).quasiMeasurePreserving.restrict hmaps).ae hGe
  have hGo : (fun p : ℝ × ℝ ↦ G (p.1, -p.2)) =ᵐ[volume.restrict U] fun p ↦ -G p := by
    filter_upwards [hGr, hGe, ho] with p hp he ho
    change G (p.1, -p.2) = d (p.1, -p.2) at hp
    rw [hp, ho, he]
  have hc := hGa.ae_continuousOn isOpen_Ioo
  have hco : ∀ᵐ x ∂(volume.restrict I),
      ContinuousOn (fun t ↦ G (x, -t)) J := by
    filter_upwards [hc] with x hx
    exact hx.comp continuous_neg.continuousOn hneg
  have hrows := ae_eqOn_sections_of_ae_eq isOpen_Ioo hGo hco
    (hc.mono fun x hx ↦ hx.neg)
  have hGzero : ∀ᵐ x ∂(volume.restrict I), G (x, 0) = 0 := by
    filter_upwards [hrows] with x hx
    apply CharZero.eq_neg_self_iff.mp
    simpa only [neg_zero] using hx 0 hz
  let Q := fun p : ℝ × ℝ ↦ G p / (p.2 : ℂ)
  have hQm : Measurable Q := by dsimp [Q]; fun_prop
  have hrowbound : ∀ᵐ x ∂(volume.restrict I),
      (∫⁻ t in J, ENNReal.ofReal (‖Q (x, t)‖ ^ 2)) ≤
        4 * ∫⁻ t in J, ENNReal.ofReal (‖dd (x, t)‖ ^ 2) := by
    filter_upwards [hGa.ae_hasIntervalH1 (hd.ae_eq hGe.symm) hdd, hGzero] with x hx hx0
    apply hx.lintegral_hardy_interior hz hx0
    intro t ht
    by_cases h : t = 0
    · simpa [h] using hx0
    · simpa only [sub_zero] using (mul_div_cancel₀ (G (x, t))
        (Complex.ofReal_ne_zero.mpr h)).symm
  have hDi := hdd.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hbound : (∫⁻ p in U, ENNReal.ofReal (‖Q p‖ ^ 2)) ≤
      4 * ∫⁻ p in U, ENNReal.ofReal (‖dd p‖ ^ 2) := by
    rw [Measure.volume_eq_prod, setLIntegral_prod _ (by fun_prop)]
    rw [setLIntegral_prod _ (by
      rw [← Measure.volume_eq_prod]
      exact ENNReal.measurable_ofReal.comp_aemeasurable hDi.aemeasurable)]
    rw [← lintegral_const_mul' _ _ (by norm_num)]
    exact lintegral_mono_ae hrowbound
  have hQi : IntegrableOn (fun p ↦ ‖Q p‖ ^ 2) U := by
    refine ⟨(hQm.norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ ↦ sq_nonneg _)]
    exact hbound.trans_lt (ENNReal.mul_lt_top (by norm_num) hDi.lintegral_lt_top)
  have hQe : Q =ᵐ[volume.restrict U] fun p ↦ d p / (p.2 : ℂ) :=
    hGe.mono fun p hp ↦ by simp [Q, hp]
  refine ⟨((memLp_two_iff_integrable_sq_norm hQm.aestronglyMeasurable).2 hQi).ae_eq hQe, ?_⟩
  have hi : (∫ p in U, ‖Q p‖ ^ 2) = ∫ p in U, ‖d p / (p.2 : ℂ)‖ ^ 2 :=
    integral_congr_ae (hQe.mono fun p hp ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hp)
  rw [← hi]
  rw [← ofReal_integral_eq_lintegral_ofReal hQi (Eventually.of_forall fun _ ↦ sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hDi (Eventually.of_forall fun _ ↦ sq_nonneg _),
    show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (4 : ℝ))] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hbound

/-- Coordinate Hardy for either axis, using specified weak derivatives
(`lem:even-h2-axis-hardy`). -/
theorem even_h2_axis_hardy {j : Fin 2} {a l r : ℝ} (ha : 0 < a) (hlr : l < r)
    {F d dd : ℝ × ℝ → ℂ} (hF : MemSobolevOn 2 (axisRectangle j a l r) F)
    (he : ∀ᵐ p ∂(volume.restrict (axisRectangle j a l r)), F (axisReflect j p) = F p)
    (hd : HasWeakPartialOn (axisRectangle j a l r) j F d)
    (hdd : HasWeakPartialOn (axisRectangle j a l r) j d dd) :
    MemLp (fun p ↦ d p / (axisCoord j p : ℂ)) 2 (volume.restrict (axisRectangle j a l r)) ∧
      (∫ p in axisRectangle j a l r, ‖d p / (axisCoord j p : ℂ)‖ ^ 2) ≤
        4 * ∫ p in axisRectangle j a l r, ‖dd p‖ ^ 2 := by
  classical
  let U := axisRectangle j a l r
  have hU : IsOpen U := by unfold U axisRectangle; split_ifs <;> exact isOpen_Ioo.prod isOpen_Ioo
  have hpre : axisReflect j ⁻¹' U = U := by
    ext p
    fin_cases j <;> simp [U, axisRectangle, axisReflect, neg_lt, and_comm]
  choose D hD _ using hF.2
  let E := fun i ↦ if i = j then d else D i
  have hE (i : Fin 2) : HasWeakPartialOn U i F (E i) := by
    by_cases hi : i = j
    · simpa [E, hi] using hd
    · simpa [E, hi] using hD i
  obtain ⟨J, hJ, hJE⟩ := hF.exists_weakJet_two_with_first hU hE
  have hJd : J [j] = d := by simp [hJE, E]
  have hJdd : HasWeakPartialOn U j d (J [j, j]) := by
    simpa only [hJd] using hJ.2 [j] (by simp) j
  have hdL : MemLp d 2 (volume.restrict U) := by
    rw [← hJd]
    exact hF.memLp_weakJet hU hJ [j] (by simp)
  have hddL : MemLp dd 2 (volume.restrict U) :=
    (hF.memLp_weakJet hU hJ [j, j] (by simp)).ae_eq
      ((ae_restrict_iff' hU.measurableSet).mpr (hJdd.ae_eq hU hdd))
  have hp := hJ.axisReflect_entries hU j hpre (c := 1)
    (he.mono fun p hp ↦ by simpa only [one_mul] using hp) [j] (by simp)
  have ho : ∀ᵐ p ∂(volume.restrict U), d (axisReflect j p) = -d p := by
    filter_upwards [hp] with p hp
    simp only [List.count_cons_self, List.count_nil, zero_add, pow_one, neg_one_mul,
      one_mul, hJd] at hp
    exact neg_eq_iff_eq_neg.mp hp
  fin_cases j
  · let V := Ioo l r ×ˢ Ioo (-a) a
    have hV : IsOpen V := isOpen_Ioo.prod isOpen_Ioo
    have hs : Prod.swap ⁻¹' U = V := by ext p; simp [U, V, axisRectangle, and_comm]
    have hm : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume := by
      rw [Measure.volume_eq_prod]
      exact Measure.measurePreserving_swap
    have hmUV : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
        (volume.restrict V) (volume.restrict U) := by
      rw [← hs]
      exact hm.restrict_preimage hU.measurableSet
    have hds := hdd.comp_swap_fst hU
    rw [hs] at hds
    have hos : ∀ᵐ p ∂(volume.restrict V), (d ∘ Prod.swap) (p.1, -p.2) =
        -(d ∘ Prod.swap) p := hmUV.quasiMeasurePreserving.ae ho
    obtain ⟨hL, hB⟩ := odd_vertical_hardy ha hlr (hdL.comp_measurePreserving hmUV)
      (hddL.comp_measurePreserving hmUV) hds hos
    have hs' : Prod.swap ⁻¹' V = U := by ext p; simp [U, V, axisRectangle, and_comm]
    have hmVU : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
        (volume.restrict U) (volume.restrict V) := by
      rw [← hs']
      exact hm.restrict_preimage hV.measurableSet
    refine ⟨?_, ?_⟩
    · simpa [U, Function.comp_def, axisCoord] using hL.comp_measurePreserving hmVU
    · have hi (f : ℝ × ℝ → ℝ) :
          (∫ p in V, f p.swap) = ∫ p in U, f p :=
        hmUV.integral_comp (Homeomorph.prodComm ℝ ℝ).measurableEmbedding f
      simpa [U, Function.comp_apply, axisCoord] using
        (hi (fun p ↦ ‖d p / (p.1 : ℂ)‖ ^ 2)).symm.le.trans
          (hB.trans_eq (congrArg (4 * ·) (hi (fun p ↦ ‖dd p‖ ^ 2))))
  · exact odd_vertical_hardy ha hlr hdL hddL hdd ho

private theorem periodize_poisson_h3 {K : Set (ℝ × ℝ)} (hc : IsCompact K)
    {w G : ℝ × ℝ → ℂ} {d e : Fin 2 → ℝ × ℝ → ℂ}
    (hw : MemLp w 2 volume) (hG : MemSobolevOn 1 univ G)
    (hd : ∀ j, MemLp (d j) 2 volume) (he : ∀ j, MemLp (e j) 2 volume)
    (hw₀ : ∀ p ∉ K, w p = 0) (hG₀ : ∀ p ∉ K, G p = 0)
    (hd₀ : ∀ j p, p ∉ K → d j p = 0) (he₀ : ∀ j p, p ∉ K → e j p = 0)
    (hwd : ∀ j, HasWeakPartialOn univ j w (d j))
    (hde : ∀ j, HasWeakPartialOn univ j (d j) (e j))
    (htrace : ∀ᵐ p, e 0 p + e 1 p = G p) : MemSobolev 3 (compactPeriodize w) := by
  have hG₂ : MemLp G 2 volume := by simpa using hG.memLp
  have hG₁ : MemSobolev 1 (compactPeriodize G) :=
    by simpa only [Nat.cast_one] using memSobolev_compactPeriodize 1 hc hG₀ hG
  have hwd' (j : Fin 2) := hasFourierPartial_compactPeriodize hc hw₀ (hd₀ j) hw (hd j) (hwd j)
  have hde' (j : Fin 2) := hasFourierPartial_compactPeriodize hc (hd₀ j) (he₀ j)
    (hd j) (he j) (hde j)
  have hLap := hasFourierLaplacian_of_second ((hasFourierPartial_iff_second (hwd' 0)).mp (hde' 0))
    ((hasFourierPartial_iff_second (hwd' 1)).mp (hde' 1))
  have heq : compactPeriodize (e 0) + compactPeriodize (e 1) = compactPeriodize G := by
    apply fourierCoeff_ext
    intro k
    rw [fourierCoeff_add, fourierCoeff_compactPeriodize hc (he₀ 0) (he 0),
      fourierCoeff_compactPeriodize hc (he₀ 1) (he 1), fourierCoeff_compactPeriodize hc hG₀ hG₂,
      ← mul_add]
    congr 1
    have hInt (j : Fin 2) : Integrable (fun p ↦ char (-k) (torusProj p) * e j p) := by
      have h := ((he j).locallyIntegrable (by norm_num)).integrableOn_isCompact hc
      have hi : Integrable (e j) := by
        rw [← integrable_indicator_iff hc.isClosed.measurableSet] at h
        exact h.congr (Eventually.of_forall fun p ↦ by
          by_cases hp : p ∈ K <;> simp [hp, he₀ j p])
      refine hi.norm.mono' (((char (-k)).continuous.comp
        isOpenQuotientMap_torusProj.continuous).aestronglyMeasurable.mul
          (he j).aestronglyMeasurable) ?_
      exact Eventually.of_forall fun p ↦ by rw [norm_mul, norm_char, one_mul]
    rw [← integral_add (hInt 0) (hInt 1)]
    apply integral_congr_ae
    filter_upwards [htrace] with p hp
    simpa only [← mul_add] using congrArg (char (-k) (torusProj p) * ·) hp
  rw [heq] at hLap
  have hInv : MemSobolev 3 (invLap (compactPeriodize G)) := by
    simpa only [show (1 : ℝ) + 2 = 3 by norm_num] using hG₁.invLap
  -- Ignore the zero mode in the comparison with the inverse Laplacian.
  apply hInv.congr_cofinite
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ × ℤ)] with k hk
  have hn : (normSq k : ℂ) ≠ 0 := by exact_mod_cast (normSq_pos k hk).ne'
  rw [fourierCoeff_invLap, ite_eq_right hk, hLap k, neg_mul, neg_neg, mul_div_cancel_left₀ _ hn]

private theorem torusProj_injOn_unitBall (x : ℝ × ℝ) :
    InjOn torusProj (Metric.ball x 1) := by
  intro p hp q hq hpq
  have hdist : dist q p < 2 := by
    have h₁ : dist p x < 1 := hp
    have h₂ : dist q x < 1 := hq
    linarith [dist_triangle_right q p x]
  obtain ⟨n, rfl⟩ := exists_liftShift_of_torusProj_eq hpq
  have hcoord (m : ℤ) (a : ℝ) (h : dist (a + m * (2 * Real.pi)) a < 2) : m = 0 := by
    by_contra hm
    have hh : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
    rw [Real.dist_eq, add_sub_cancel_left, abs_mul,
      abs_of_pos (show 0 < 2 * Real.pi by positivity)] at h
    nlinarith [Real.pi_gt_three, mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ 2 * Real.pi)]
  rw [Prod.dist_eq, max_lt_iff] at hdist
  have hn : n = 0 := Prod.ext (hcoord n.1 p.1 hdist.1) (hcoord n.2 p.2 hdist.2)
  rw [hn, liftShift_zero]

/-- Interior elliptic H³ regularity, with the Laplacian identified weakly
(the regularity part of `lem:elliptic-local`). -/
theorem elliptic_local_h3 {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u F : ℝ × ℝ → ℂ}
    {D : List (Fin 2) → ℝ × ℝ → ℂ} (hu : MemSobolevLocOn 2 U u)
    (hF : MemSobolevLocOn 1 U F) (hD : HasWeakJetOn 2 U u D)
    (hΔ : ∀ᵐ p ∂(volume.restrict U), D [0, 0] p + D [1, 1] p = F p) :
    MemSobolevLocOn 3 U u := by
  apply memSobolevLocOn_of_locally_ae
  intro x hx
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  let ρ := min r 1 / 2
  have hρ : 0 < ρ := half_pos (lt_min hr zero_lt_one)
  let B := Metric.ball x ρ
  let b : ContDiffBump x := ⟨ρ / 4, ρ / 2, by positivity, by linarith⟩
  let χ : ℝ × ℝ → ℂ := fun p ↦ b p
  let K := tsupport χ
  have hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hc : IsCompact K := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hKB : K ⊆ B := by
    refine (tsupport_comp_subset Complex.ofReal_zero b).trans ?_
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by linarith : ρ / 2 < ρ)
  have hB : B ⊆ U := (Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall (by dsimp [ρ]; linarith [min_le_left r 1]))).trans hrU
  have hKU := hKB.trans hB
  let w : ℝ × ℝ → ℂ := fun p ↦ χ p * u p
  let a (j : Fin 2) := coordPartial j χ
  let A (j : Fin 2) := coordPartial j (a j)
  let d (j : Fin 2) : ℝ × ℝ → ℂ := fun p ↦ a j p * u p + χ p * D [j] p
  let e (j : Fin 2) : ℝ × ℝ → ℂ := fun p ↦
    (A j p * u p + a j p * D [j] p) + (a j p * D [j] p + χ p * D [j,j] p)
  let G : ℝ × ℝ → ℂ := fun p ↦
    ((A 0 p * u p + a 0 p * D [0] p) + a 0 p * D [0] p) +
    ((A 1 p * u p + a 1 p * D [1] p) + a 1 p * D [1] p) + χ p * F p
  have ha (j : Fin 2) := contDiff_coordPartial_top j hχ
  have hA (j : Fin 2) := contDiff_coordPartial_top j (ha j)
  have has (j : Fin 2) : tsupport (a j) ⊆ K := tsupport_coordPartial_subset j χ
  have hAs (j : Fin 2) : tsupport (A j) ⊆ K :=
    (tsupport_coordPartial_subset j (a j)).trans (has j)
  have hac (j : Fin 2) : HasCompactSupport (a j) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (has j)
  have hwd (j : Fin 2) : HasWeakPartialOn univ j w (d j) := by
    have hj := hD.2 [] (by simp) j
    rw [hD.1] at hj
    exact hj.cutoff hχ hc hKU _
  have hde (j : Fin 2) : HasWeakPartialOn univ j (d j) (e j) := by
    have hj := hD.2 [] (by simp) j
    rw [hD.1] at hj
    exact (hj.cutoff (ha j) (hac j) ((has j).trans hKU) _).add
      ((hD.2 [j] (by simp) j).cutoff hχ hc hKU _)
  have hc₀ (f : ℝ × ℝ → ℂ) (hf : tsupport f ⊆ K) (p : ℝ × ℝ) (hp : p ∉ K) : f p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hp (hf h))
  have hw₀ (p : ℝ × ℝ) (hp : p ∉ K) : w p = 0 := by simp [w, hc₀ χ (subset_refl _) p hp]
  have hzero (p : ℝ × ℝ) (hp : p ∉ K) :
      χ p = 0 ∧ (∀ j, a j p = 0) ∧ (∀ j, A j p = 0) :=
    ⟨hc₀ χ (subset_refl _) p hp, fun j ↦ hc₀ (a j) (has j) p hp,
      fun j ↦ hc₀ (A j) (hAs j) p hp⟩
  have hd₀ (j : Fin 2) (p : ℝ × ℝ) (hp : p ∉ K) : d j p = 0 := by
    obtain ⟨h₁, h₂, -⟩ := hzero p hp
    simp [d, h₁, h₂]
  have he₀ (j : Fin 2) (p : ℝ × ℝ) (hp : p ∉ K) : e j p = 0 := by
    obtain ⟨h₁, h₂, h₃⟩ := hzero p hp
    simp [e, h₁, h₂, h₃]
  have hG₀ (p : ℝ × ℝ) (hp : p ∉ K) : G p = 0 := by
    obtain ⟨h₁, h₂, h₃⟩ := hzero p hp
    simp [G, h₁, h₂, h₃]
  have hs (k : ℕ) {f g : ℝ × ℝ → ℂ} (hf : MemSobolevLocOn k U f)
      (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgs : tsupport g ⊆ K) :
      MemSobolevOn k univ (fun p ↦ g p * f p) :=
    hf.cutoff k hU hg (hc.of_isClosed_subset (isClosed_tsupport _) hgs) (hgs.trans hKU)
  have hLp {f : ℝ × ℝ → ℂ} {k : ℕ} (hf : MemSobolevOn k univ f) : MemLp f 2 volume := by
    simpa only [Measure.restrict_univ] using hf.memLp
  have hD₁ (j : Fin 2) : MemSobolevLocOn 1 U (D [j]) :=
    hD.memSobolevLocOn hu [j] (by simp) (by simp)
  have hw := hLp (hs 2 hu hχ (subset_refl K))
  have hd (j : Fin 2) : MemLp (d j) 2 volume :=
    hLp ((hs 1 hu.of_succ (ha j) (has j)).add (hs 1 (hD₁ j) hχ (subset_refl K)))
  have he (j : Fin 2) : MemLp (e j) 2 volume := by
    have h₁ := hLp (hs 0 hu.of_succ.of_succ (hA j) (hAs j))
    have h₂ := hLp (hs 0 (hD₁ j).of_succ (ha j) (has j))
    have hD₂ : MemSobolevLocOn 0 U (D [j, j]) :=
      hD.memSobolevLocOn hu [j, j] (by simp) (by simp)
    have h₃ := hLp (hs 0 hD₂ hχ (subset_refl K))
    exact (h₁.add h₂).add (h₂.add h₃)
  have hG : MemSobolevOn 1 univ G := by
    have hj (j : Fin 2) := ((hs 1 hu.of_succ (hA j) (hAs j)).add
      (hs 1 (hD₁ j) (ha j) (has j))).add (hs 1 (hD₁ j) (ha j) (has j))
    exact ((hj 0).add (hj 1)).add (hs 1 hF hχ (subset_refl K))
  have htrace : ∀ᵐ p, e 0 p + e 1 p = G p := by
    filter_upwards [(ae_restrict_iff' hU.measurableSet).mp hΔ] with p hp
    by_cases hpK : p ∈ K
    · dsimp [e, G]
      linear_combination χ p * hp (hKU hpK)
    · rw [he₀ 0 p hpK, he₀ 1 p hpK, hG₀ p hpK, add_zero]
  have h₃ := periodize_poisson_h3 hc hw hG hd he hw₀ hG₀ hd₀ he₀ hwd hde htrace
  let V := Metric.ball x (ρ / 4)
  have hVB : V ⊆ B := Metric.ball_subset_ball (by linarith)
  have hinj : InjOn torusProj B := (torusProj_injOn_unitBall x).mono
    (Metric.ball_subset_ball (by dsimp [ρ]; linarith [min_le_right r 1]))
  refine ⟨V, Metric.isOpen_ball, Metric.mem_ball_self (by positivity),
    liftL2 (compactPeriodize w), (memSobolevOn_liftL2 h₃ Metric.isBounded_ball).memSobolevLocOn, ?_⟩
  filter_upwards [ae_restrict_of_ae (liftL2_compactPeriodize hc hw₀ hw),
    ae_restrict_mem (Metric.isOpen_ball (x := x) (ε := ρ / 4)).measurableSet] with p hp hpV
  have hpB := hVB hpV
  rw [hp, liftPeriodize, finsum_eq_single _ (0 : ℤ × ℤ) (fun n hn ↦ ?_), liftShift_zero]
  · have hone : b p = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hpV)
    simp [w, χ, hone]
  · by_contra hn₀
    have hm : liftShift n p ∈ K := by_contra fun h ↦ hn₀ (hw₀ _ h)
    have hnp := hinj (hKB hm) hpB (torusProj_liftShift n p)
    apply hn
    have h₁ := congrArg Prod.fst hnp
    have h₂ := congrArg Prod.snd hnp
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    exact Prod.ext (by simpa [liftShift, hpi] using h₁) (by simpa [liftShift, hpi] using h₂)

private theorem tendsto_squareEnergy_of_L2 {V : Set (ℝ × ℝ)} {v : ℕ → ℝ × ℝ → ℂ}
    {f : ℝ × ℝ → ℂ} (hv : ∀ n, MemLp (v n) 2 (volume.restrict V))
    (hf : MemLp f 2 (volume.restrict V))
    (ht : Tendsto (fun n ↦ eLpNorm (fun p ↦ v n p - f p) 2 (volume.restrict V)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ squareEnergy V (v n)) atTop (𝓝 (squareEnergy V f)) := by
  let c : ℝ × ℝ → ℂ := fun _ ↦ 1
  have hc : MemLp c ⊤ (volume.restrict V) := memLp_top_const _
  have hi {g : ℝ × ℝ → ℂ} (hg : MemLp g 2 (volume.restrict V)) :
      (∫ p in V, c p * g p * (starRingEnd ℂ) (g p)).re = squareEnergy V g := by
    have hm : MemLp (fun p ↦ (starRingEnd ℂ) (g p)) 2 (volume.restrict V) := by
      apply hg.of_le_mul (c := 1)
        (Complex.conjCLE.continuous.comp_aestronglyMeasurable hg.aestronglyMeasurable)
      exact Eventually.of_forall fun p ↦ by simp
    have hi : IntegrableOn (fun p ↦ c p * g p * (starRingEnd ℂ) (g p)) V := by
      simp only [c, one_mul]
      exact hg.integrable_mul hm
    have he := (integral_re hi).symm
    change (∫ p in V, c p * g p * (starRingEnd ℂ) (g p)).re =
      ∫ p in V, (c p * g p * (starRingEnd ℂ) (g p)).re at he
    rw [he]
    apply integral_congr_ae
    exact Eventually.of_forall fun p ↦ by
      change (c p * g p * (starRingEnd ℂ) (g p)).re = ‖g p‖ ^ 2
      rw [show c p = 1 from rfl, one_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      exact Complex.ofReal_re _
  have := Complex.continuous_re.tendsto _ |>.comp
    (tendsto_integral_mul_conj_of_L2 hc hv hv hf hf ht ht)
  rw [hi hf] at this
  convert this using 1
  funext n
  exact (hi (hv n)).symm

private theorem tendsto_eLpNorm_sum_diff {V : Set (ℝ × ℝ)} {v w : ℕ → ℝ × ℝ → ℂ}
    {f g : ℝ × ℝ → ℂ}
    (htv : Tendsto (fun n ↦ eLpNorm (fun p ↦ v n p - f p) 2 (volume.restrict V)) atTop (𝓝 0))
    (htw : Tendsto (fun n ↦ eLpNorm (fun p ↦ w n p - g p) 2 (volume.restrict V)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun p ↦ (v n p + w n p) - (f p + g p)) 2 (volume.restrict V))
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using htv.add htw) (fun _ ↦ show (0 : ENNReal) ≤ _ from bot_le)
  intro n
  have he : (fun p ↦ v n p + w n p - (f p + g p)) =
      (fun p ↦ v n p - f p) + (fun p ↦ w n p - g p) := by
    funext p
    simp only [Pi.add_apply]
    ring
  change eLpNorm (fun p ↦ v n p + w n p - (f p + g p)) 2 (volume.restrict V) ≤ _
  rw [he]
  exact eLpNorm_add_le (p := (2 : ENNReal)) (by norm_num)

/-- Uniform squared dyadic elliptic estimate (`lem:elliptic-dyadic`). -/
theorem elliptic_dyadic : ∃ C : ℝ, 0 < C ∧ ∀ (c : ℝ × ℝ) (r : ℝ), 0 < r →
    ∀ (u F : ℝ × ℝ → ℂ) (D G : List (Fin 2) → ℝ × ℝ → ℂ),
      let A := {p | r < localRadius c p ∧ localRadius c p < 2 * r}
      let B := {p | r / 2 < localRadius c p ∧ localRadius c p < 4 * r}
      MemSobolevOn 2 B u → MemSobolevOn 1 B F →
      HasWeakJetOn 3 B u D → HasWeakJetOn 1 B F G →
      (∀ᵐ p ∂(volume.restrict B), D [0, 0] p + D [1, 1] p = F p) →
      RadialJetLp 3 0 A c D ∧
        radialJetEnergy 3 0 A c D ≤ C * (radialJetEnergy 1 0 B c G +
          r⁻¹ ^ 2 * radialJetEnergy 0 0 B c G + r⁻¹ ^ 6 * radialJetEnergy 0 0 B c D) := by
  obtain ⟨C, hC, hbound⟩ := smooth_dyadic_third_estimate
  refine ⟨8 * C, by positivity, ?_⟩
  intro c r hr u F D G A B hu hF hD hG hΔ
  let V := ellipticAnnulus c (r * (3 / 4)) (r * 3)
  have hA : IsOpen A := isOpen_ellipticAnnulus c _ _
  have hB : IsOpen B := isOpen_ellipticAnnulus c _ _
  have hV : IsOpen V := isOpen_ellipticAnnulus c _ _
  have hVc : IsCompact (closure V) := isCompact_closure_ellipticAnnulus c _ _
  have hVB : closure V ⊆ B := closure_ellipticAnnulus_subset
    (by linarith) (by linarith)
  have hAv : A ⊆ V := by
    rintro p ⟨hp, hq⟩
    exact ⟨lt_trans (by linarith) hp, hq.trans (by linarith)⟩
  have hVB' := subset_closure.trans hVB
  have hD₂ : HasWeakJetOn 2 B u D := ⟨hD.1, fun w hw ↦ hD.2 w (by omega)⟩
  have hu₃ : MemSobolevLocOn 3 B u :=
    elliptic_local_h3 hB hu.memSobolevLocOn hF.memSobolevLocOn hD₂ hΔ
  obtain ⟨E, hE, hEL, v, hv, hvL⟩ := local_smooth_approximation 3 hB hV hVc hVB hu₃
  have hED (w : List (Fin 2)) (hw : w.length ≤ 3) : E w =ᵐ[volume.restrict V] D w :=
    (ae_restrict_iff' hV.measurableSet).mpr (hE.ae_eq hV (hD.mono hVB') w hw)
  have hDL (w : List (Fin 2)) (hw : w.length ≤ 3) := (hEL w hw).ae_eq (hED w hw)
  have hlim (w : List (Fin 2)) (hw : w.length ≤ 3) :
      Tendsto (fun n ↦ eLpNorm (fun p ↦ classicalComplexJet w (v n) p - D w p)
        2 (volume.restrict V)) atTop (𝓝 0) := by
    convert (hvL w hw).2 using 1
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [hED w hw] with p hp
    rw [hp]
  have hGL (w : List (Fin 2)) (hw : w.length ≤ 1) := hF.memLp_weakJet hB hG w hw
  have hΔV : ∀ᵐ p ∂volume.restrict V, D [0, 0] p + D [1, 1] p = G [] p := by
    rw [hG.1]
    exact ae_mono (Measure.restrict_mono hVB' le_rfl) hΔ
  have hΔj (j : Fin 2) :
      ∀ᵐ p ∂volume.restrict V, D [j, 0, 0] p + D [j, 1, 1] p = G [j] p := by
    have hh := (((hD.2 [0, 0] (by simp) j).add (hD.2 [1, 1] (by simp) j)).mono hVB')
      |>.congr_ae_on hV.measurableSet ((ae_restrict_iff' hV.measurableSet).mp hΔV)
        (Eventually.of_forall fun _ _ ↦ rfl)
    exact (ae_restrict_iff' hV.measurableSet).mpr
      (hh.ae_eq hV ((hG.2 [] (by simp) j).mono hVB'))
  have hsum {i j : List (Fin 2)} (hi : i.length ≤ 3) (hj : j.length ≤ 3)
      {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 (volume.restrict V))
      (he : ∀ᵐ p ∂volume.restrict V, D i p + D j p = f p) :
      Tendsto (fun n ↦ squareEnergy V (fun p ↦
        classicalComplexJet i (v n) p + classicalComplexJet j (v n) p)) atTop
          (𝓝 (squareEnergy V f)) := by
    apply tendsto_squareEnergy_of_L2 (fun n ↦ ((hvL i hi).1 n).add ((hvL j hj).1 n)) hf
    have h := tendsto_eLpNorm_sum_diff (hlim i hi) (hlim j hj)
    convert h using 1
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [he] with p hp
    simp only [Pi.add_apply, hp]
  have hlimL : Tendsto (fun n ↦ squareEnergy V (energyLaplacian (v n))) atTop
      (𝓝 (squareEnergy V (G []))) :=
    hsum (i := [0, 0]) (j := [1, 1]) (by simp) (by simp)
      ((hGL [] (by simp)).mono_measure (Measure.restrict_mono hVB' le_rfl)) hΔV
  have hlimLj (k : Fin 2) :
      Tendsto (fun n ↦ squareEnergy V (coordPartial k (energyLaplacian (v n)))) atTop
        (𝓝 (squareEnergy V (G [k]))) := by
    have h := hsum (i := [k, 0, 0]) (j := [k, 1, 1]) (by simp) (by simp)
      ((hGL [k] (by simp)).mono_measure (Measure.restrict_mono hVB' le_rfl)) (hΔj k)
    convert h using 1
    funext n
    congr 1
    unfold energyLaplacian
    have hd (j : Fin 2) := contDiff_coordPartial_top j (contDiff_coordPartial_top j (hv n).1)
    exact coordPartial_sum k ((hd 0).differentiable (by simp)) ((hd 1).differentiable (by simp))
  have hlim0 : Tendsto (fun n ↦ squareEnergy V (v n)) atTop (𝓝 (squareEnergy V (D []))) :=
    tendsto_squareEnergy_of_L2 ((hvL [] (by simp)).1) (hDL [] (by simp)) (hlim [] (by simp))
  have hlimA (w : List (Fin 2)) (hw : w.length ≤ 3) :
      Tendsto (fun n ↦ squareEnergy A (classicalComplexJet w (v n))) atTop
        (𝓝 (squareEnergy A (D w))) := by
    have hm := Measure.restrict_mono hAv (le_refl (volume : Measure (ℝ × ℝ)))
    apply tendsto_squareEnergy_of_L2 (fun n ↦ ((hvL w hw).1 n).mono_measure hm)
      ((hDL w hw).mono_measure hm)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hlim w hw)
      (fun _ ↦ bot_le) (fun _ ↦ eLpNorm_mono_measure _ hm)
  have hbnd (i j k : Fin 2) : squareEnergy A (D [i, j, k]) ≤ C *
      (squareEnergy V (G [k]) + r⁻¹ ^ 2 * squareEnergy V (G []) +
        r⁻¹ ^ 6 * squareEnergy V (D [])) := by
    apply le_of_tendsto_of_tendsto (hlimA [i, j, k] (by simp))
      (((hlimLj k).add (hlimL.const_mul _)).add (hlim0.const_mul _) |>.const_mul C)
    exact Eventually.of_forall fun n ↦ hbound c r hr (hv n).1 i j k
  have hmono {f : ℝ × ℝ → ℂ} (hf : MemLp f 2 (volume.restrict B)) :
      squareEnergy V f ≤ squareEnergy B f :=
    setIntegral_mono_set hf.norm.integrable_sq (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (Eventually.of_forall hVB')
  have hBk (k : Fin 2) : squareEnergy V (G [k]) ≤ radialJetEnergy 1 0 B c G := by
    refine (hmono (hGL [k] (by simp))).trans ?_
    have h₁ : radialJetEnergy 1 0 B c G = squareEnergy B (G [0]) + squareEnergy B (G [1]) := by
      unfold radialJetEnergy
      simp only [pow_zero, div_one]
      trans ∑ j : Fin 2, squareEnergy B (G [j])
      · exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2)) _ _ (fun f ↦ by
          simp [List.ofFn_succ, squareEnergy])
      · exact Fin.sum_univ_two _
    rw [h₁]
    fin_cases k
    · exact le_add_of_nonneg_right (squareEnergy_nonneg _ _)
    · exact le_add_of_nonneg_left (squareEnergy_nonneg _ _)
  have hE0 (J : List (Fin 2) → ℝ × ℝ → ℂ) :
      radialJetEnergy 0 0 B c J = squareEnergy B (J []) := by
    simp [radialJetEnergy, squareEnergy, List.ofFn_zero]
  have hB0 := hmono (hGL [] (by simp))
  have hBu := hmono (show MemLp (D []) 2 (volume.restrict B) from by rw [hD.1]; exact hu.memLp)
  refine ⟨fun w hw ↦ ?_, ?_⟩
  · simpa only [pow_zero, Complex.ofReal_one, div_one] using
      (hDL w hw.le).mono_measure (Measure.restrict_mono hAv le_rfl)
  · have hE₃ : radialJetEnergy 3 0 A c D =
        ∑ w : Fin 3 → Fin 2, squareEnergy A (D (List.ofFn w)) := by
      simp only [radialJetEnergy, pow_zero, div_one, squareEnergy]
    rw [hE₃]
    calc
      _ ≤ ∑ _w : Fin 3 → Fin 2, C *
          (radialJetEnergy 1 0 B c G + r⁻¹ ^ 2 * radialJetEnergy 0 0 B c G +
            r⁻¹ ^ 6 * radialJetEnergy 0 0 B c D) := by
        apply Finset.sum_le_sum
        intro w _
        have h := hbnd (w 0) (w 1) (w 2)
        have hw : List.ofFn w = [w 0, w 1, w 2] := by
          simp [List.ofFn_succ]
        rw [hw]
        refine h.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
        rw [hE0 G, hE0 D]
        gcongr
        exact hBk (w 2)
      _ = _ := by simp [radialJetEnergy, mul_assoc]




end NoEmbeddedEigenvalues
