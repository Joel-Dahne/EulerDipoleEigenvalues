import NoEmbeddedEigenvalues.Regularity.OddOddRegularity
import NoEmbeddedEigenvalues.SaddleChartPullback
import NoEmbeddedEigenvalues.PeriodicSobolev
import NoEmbeddedEigenvalues.SobolevMultipliers

/-!
# Assembly of local stream quotients

Blueprint: proof of `prop:dd-stream-quotient-h2`.

Local division, weighted point removal and smooth inverse multiplication are
performed before gluing the periodic raw quotient. Values on the separatrix
are only compared almost everywhere.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set
open scoped ContDiff

private theorem sobolev_of_weighted_jet {n : ℕ} {c : ℝ × ℝ} {r : ℝ}
    {f : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn n (localDisk c r) f D)
    (hw : ∀ k ≤ n, RadialJetLp k (n + 1 - k) (localDisk c r) c D) :
    MemSobolevOn n (localDisk c r) f := by
  apply memSobolevOn_iff_exists_weakJet.mpr
  refine ⟨D, hD, fun w hw' ↦ ?_⟩
  exact memLp_of_div_localRadius_pow (hw w.length hw' w rfl)

private theorem loc_comp_symm {A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)} {c : ℝ × ℝ}
    (hm : MeasurePreserving (planeAffine A c)) {k : ℕ} {U : Set (ℝ × ℝ)}
    {f : ℝ × ℝ → ℂ} (hf : MemSobolevLocOn k U f) :
    MemSobolevLocOn k ((planeAffine A c).symm ⁻¹' U) (f ∘ (planeAffine A c).symm) := by
  have heq : ((planeAffine A c).symm : (ℝ × ℝ) → ℝ × ℝ) =
      planeAffine A.symm (-A.symm c) := by
    funext p
    change A.symm (p - c) = A.symm p + -A.symm c
    simpa only [sub_eq_add_neg] using A.symm.map_sub p c
  have hmi : MeasurePreserving (planeAffine A.symm (-A.symm c)) := by
    rw [← heq]
    exact MeasurePreserving.symm (planeAffine A c).toMeasurableEquiv hm
  simpa only [← heq] using hf.comp_planeAffine A.symm (-A.symm c) hmi

private theorem patch_of_comp {A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)} {c : ℝ × ℝ}
    (hm : MeasurePreserving (planeAffine A c)) {k : ℕ} {f : ℝ × ℝ → ℂ} {q : ℝ × ℝ}
    (hf : ∃ U, IsOpen U ∧ q ∈ U ∧ MemSobolevLocOn k U (f ∘ planeAffine A c)) :
    ∃ W, IsOpen W ∧ planeAffine A c q ∈ W ∧ MemSobolevLocOn k W f := by
  obtain ⟨U, hU, hq, hf⟩ := hf
  refine ⟨(planeAffine A c).symm ⁻¹' U, hU.preimage (planeAffine A c).symm.continuous,
    by change (planeAffine A c).symm (planeAffine A c q) ∈ U
       rwa [(planeAffine A c).symm_apply_apply], ?_⟩
  convert loc_comp_symm hm hf using 1
  ext p
  exact congrArg f ((planeAffine A c).apply_symm_apply p).symm

/-! ### Null separatrix and lifted parity -/

/-- The dipole vanishes only on a null set. -/
theorem ae_Ψ_ne_zero : ∀ᵐ t : Torus, Ψ t ≠ 0 := by
  have hΨ : Continuous Ψ :=
    (Real.Angle.continuous_cos.comp continuous_fst).add
      (Real.Angle.continuous_cos.comp continuous_snd)
  have hsingle (x : Real.Angle) : volume ({x} : Set Real.Angle) = 0 := by
    change (volume : Measure (AddCircle (2 * Real.pi))) {x} = 0
    have hx := AddCircle.volume_closedBall (T := 2 * Real.pi) (x := x) (ε := 0)
    have hx0 : (volume : Measure (AddCircle (2 * Real.pi))) (Metric.closedBall x 0) = 0 := by
      simpa only [mul_zero, min_eq_right (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
        ENNReal.ofReal_zero] using hx
    exact measure_mono_null
      (singleton_subset_iff.mpr (Metric.mem_closedBall_self (by norm_num))) hx0
  have hnull : ∀ᵐ t : Torus, Ψ t ≠ 0 := by
    rw [Measure.volume_eq_prod]
    apply (Measure.ae_prod_iff_ae_ae
      (isClosed_eq hΨ continuous_const).isOpen_compl.measurableSet).2
    exact Filter.Eventually.of_forall fun x ↦ by
      rw [ae_iff]
      simp only [not_not]
      have hsub : {y : Real.Angle | Ψ (x, y) = 0} ⊆
          {((Real.pi : ℝ) : Real.Angle) - x, x - ((Real.pi : ℝ) : Real.Angle)} := by
        intro y hy
        rcases Ψ_eq_zero_iff (x, y) |>.mp hy with hy | hy
        · exact Or.inl (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hy))
        · exact Or.inr (eq_sub_iff_add_eq.mpr
            (by simpa [add_comm] using (sub_eq_iff_eq_add.mp hy).symm))
      have hpair := measure_union_null (hsingle (((Real.pi : ℝ) : Real.Angle) - x))
        (hsingle (x - ((Real.pi : ℝ) : Real.Angle)))
      exact measure_mono_null hsub (by simpa only [singleton_union] using hpair)
  exact hnull

private theorem ae_dipole_ne_zero : ∀ᵐ p, dipoleLift p ≠ 0 := by
  simpa only [Ψ_torusProj] using ae_torusProj ae_Ψ_ne_zero

/-! ### Saddle patches -/

private theorem saddle_quotient_patch {lam : ℝ} (hlam : lam ≠ 0) {ζ : L2}
    (hζ : IsEigenSolution lam ζ) (hs : InSector false false ζ)
    {P : ℝ × ℝ} (hP : P ∈ saddleSet) :
    ∃ W, IsOpen W ∧ P ∈ W ∧ MemSobolevLocOn 2 W
      (fun p ↦ contStream ζ p / (dipoleLift p : ℂ)) := by
  obtain ⟨r, hr, a, D₀, D, _, hD, _, hw⟩ := dd_weighted_third_stream hlam hζ hs P hP
  have hR := sobolev_of_weighted_jet hD hw
  obtain ⟨E, hR', hE, hw'⟩ := saddle_chart_pullback hP hR hD
  have hodd : ∀ j, ∀ᵐ q ∂(volume.restrict (localDisk 0 r)),
      (contStream ζ (saddleOrthoChart P (axisReflect j q)) -
        a * (dipoleLift (saddleOrthoChart P (axisReflect j q)) : ℂ)) =
      -(contStream ζ (saddleOrthoChart P q) -
        a * (dipoleLift (saddleOrthoChart P q) : ℂ)) := by
    intro j
    filter_upwards [ae_restrict_of_ae (contStream_chart_parity hP hs j)] with q hq
    rw [hq, saddle_dipole_factorization hP, saddle_dipole_factorization hP,
      saddleFactor_regular.2.2.1 j]
    fin_cases j <;> simp [axisReflect] <;> ring
  obtain ⟨C, _, hdiv⟩ := weighted_double_division hr
  obtain ⟨V, G, hV, hG, hmul, h0, h1, h2, _⟩ :=
    hdiv _ E hR' hE hodd (hw' 1 3 (hw 1 (by omega)))
      (hw' 2 2 (hw 2 (by omega))) (hw' 3 1 (hw 3 (by omega)))
  have hV' := (weighted_h2_point_removal hr hV hG h0 h1 h2).1
  let U := localDisk 0 r ∩ {q | saddleFactor q ≠ 0}
  have ho : IsOpen U := (isOpen_localDisk 0 r).inter
    (isOpen_ne_fun saddleFactor_regular.1.continuous continuous_const)
  have hu : (0 : ℝ × ℝ) ∈ U := by
    simp [U, localDisk, localRadius, hr, saddleFactor_regular.2.1]
  have hQ : MemSobolevLocOn 2 U (fun q ↦ a + V q / (saddleFactor q : ℂ)) :=
    (memSobolevLocOn_of_contDiff 2 U contDiff_const).add
      ((hV'.memSobolevLocOn.mono inter_subset_left).div_smooth ho saddleFactor_regular.1
        (fun _ hq ↦ hq.2))
  have hae : (fun q ↦ a + V q / (saddleFactor q : ℂ)) =ᵐ[volume.restrict U]
      (fun q ↦ contStream ζ (saddleOrthoChart P q) /
        (dipoleLift (saddleOrthoChart P q) : ℂ)) := by
    have hm := ae_restrict_of_ae_restrict_of_subset
      (inter_subset_left (t := {q | saddleFactor q ≠ 0})) hmul
    filter_upwards [hm, ae_restrict_of_ae
      ((measurePreserving_saddleChart hP).quasiMeasurePreserving.ae ae_dipole_ne_zero)] with q hq hn
    have hn' : (dipoleLift (saddleOrthoChart P q) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
    have hm' : (saddleFactor q : ℂ) ≠ 0 := by
      intro hz
      apply hn'
      rw [saddle_dipole_factorization hP]
      push_cast
      rw [hz, mul_zero]
    apply (eq_div_iff hn').mpr
    change contStream ζ (saddleOrthoChart P q) - a *
      (dipoleLift (saddleOrthoChart P q) : ℂ) = _ at hq
    calc
      _ = a * (dipoleLift (saddleOrthoChart P q) : ℂ) +
          ((q.1 * q.2 : ℝ) : ℂ) * V q := by
        rw [saddle_dipole_factorization hP]
        push_cast
        field_simp
      _ = _ := by linear_combination -hq
  have hpatch := patch_of_comp
    (A := saddleLinear P hP) (c := P)
    (by simpa only [planeAffine_saddleLinear P hP] using measurePreserving_saddleChart hP)
    (f := fun p ↦ contStream ζ p / (dipoleLift p : ℂ)) (q := 0) (by
      refine ⟨U, ho, hu, ?_⟩
      rw [planeAffine_saddleLinear P hP]
      exact hQ.congr_ae_on ((ae_restrict_iff' ho.measurableSet).mp hae))
  simpa only [planeAffine_saddleLinear P hP, saddleOrthoChart, Prod.fst_zero, Prod.snd_zero,
    mul_zero, sub_self, zero_add, add_zero, zero_div] using hpatch

/-! ### Regular separatrix patches -/

private theorem separatrix_axis_chart {p : ℝ × ℝ} (hp : dipoleLift p = 0) :
    ∃ n : ℤ, Odd n ∧ ∃ e : Bool, ∃ t : ℝ,
      p = saddleOrthoChart (0, n * Real.pi) (if e then (0, t) else (t, 0)) := by
  have hz : Real.cos ((p.1 + p.2) / 2) * Real.cos ((p.1 - p.2) / 2) = 0 := by
    have h := Real.cos_add_cos p.1 p.2
    change Real.cos p.1 + Real.cos p.2 = 0 at hp
    nlinarith
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  rcases mul_eq_zero.mp hz with h | h
  · obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp h
    refine ⟨2 * k + 1, ⟨k, by ring⟩, true, -Real.sqrt 2 * p.1, ?_⟩
    ext <;> simp [saddleOrthoChart]
    field_simp
    nlinarith [hk]
  · obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp h
    refine ⟨-(2 * k + 1), ⟨-k - 1, by ring⟩, false, Real.sqrt 2 * p.1, ?_⟩
    ext <;> simp [saddleOrthoChart]
    field_simp
    nlinarith [hk]

private theorem bad_axis_point_is_saddle {n : ℤ} (hn : Odd n) (e : Bool) {t : ℝ}
    (hb : t * saddleFactor (t, 0) = 0) :
    saddleOrthoChart (0, n * Real.pi) (if e then (0, t) else (t, 0)) ∈ saddleSet := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hsin : Real.sin (t / Real.sqrt 2) = 0 := by
    by_cases ht : t = 0
    · simp [ht]
    have htd : t / Real.sqrt 2 ≠ 0 := div_ne_zero ht hs
    have hb' : Real.sinc (t / Real.sqrt 2) = 0 := by
      simpa [saddleFactor, ht] using (mul_eq_zero.mp hb).resolve_left ht
    rw [Real.sinc_of_ne_zero htd] at hb'
    exact (div_eq_zero_iff.mp hb').resolve_right htd
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hsin
  rcases hn with ⟨k, hk⟩
  cases e
  · refine ⟨m, n + m, ⟨k + m, by omega⟩, ?_⟩
    simp [saddleOrthoChart, ← hm, Int.cast_add, add_mul]
  · refine ⟨-m, n + m, ⟨k, by omega⟩, ?_⟩
    simp [saddleOrthoChart, neg_div, ← hm, Int.cast_add, Int.cast_neg, add_mul]

private theorem exists_axisRectangle {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {t : ℝ} (ht : (t, 0) ∈ U) :
    ∃ b l r : ℝ, 0 < b ∧ l < r ∧ (t, 0) ∈ axisRectangle 1 b l r ∧
      IsCompact (closure (axisRectangle 1 b l r)) ∧
      closure (axisRectangle 1 b l r) ⊆ U := by
  obtain ⟨d, hd, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds ht)
  refine ⟨d, t - d, t + d, hd, by linarith, ?_, ?_, ?_⟩
  · simp [axisRectangle, hd]
  · simp only [axisRectangle, Fin.isValue, one_ne_zero, ↓reduceIte, closure_prod_eq,
      closure_Ioo (by linarith : t - d ≠ t + d), closure_Ioo (by linarith : -d ≠ d)]
    exact isCompact_Icc.prod isCompact_Icc
  · apply Subset.trans _ hsub
    simp only [axisRectangle, Fin.isValue, one_ne_zero, ↓reduceIte, closure_prod_eq,
      closure_Ioo (by linarith : t - d ≠ t + d), closure_Ioo (by linarith : -d ≠ d)]
    intro q hq
    rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq,
      sub_zero, abs_le, abs_le]
    constructor <;> constructor <;> linarith [hq.1.1, hq.1.2, hq.2.1, hq.2.2]

private theorem regular_quotient_in_chart {A : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)} {c : ℝ × ℝ}
    (hm : MeasurePreserving (planeAffine A c)) {f : ℝ × ℝ → ℂ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hf : MemSobolevLocOn 3 U (f ∘ planeAffine A c))
    (hodd : ∀ᵐ q, f (planeAffine A c (axisReflect 1 q)) = -f (planeAffine A c q))
    (hfac : ∀ q, dipoleLift (planeAffine A c q) = q.2 * (q.1 * saddleFactor q))
    {t : ℝ} (ht : (t, 0) ∈ U) (hb : t * saddleFactor (t, 0) ≠ 0) :
    ∃ W, IsOpen W ∧ planeAffine A c (t, 0) ∈ W ∧ MemSobolevLocOn 2 W
      (fun p ↦ f p / (dipoleLift p : ℂ)) := by
  obtain ⟨b, l, r, hb0, hlr, htR, hcR, hRU⟩ := exists_axisRectangle hU ht
  have hoR : IsOpen (axisRectangle 1 b l r) := by
    simp only [axisRectangle, Fin.isValue, one_ne_zero, ↓reduceIte]
    exact isOpen_Ioo.prod isOpen_Ioo
  have hfR := hf _ hoR hcR hRU
  obtain ⟨D, hD, _⟩ := memSobolevOn_iff_exists_weakJet.mp hfR
  obtain ⟨C, _, hdiv⟩ := odd_h3_division hlr hb0
  obtain ⟨V, E, hV, _, hid, _, _⟩ := hdiv _ D hfR hD (ae_restrict_of_ae hodd)
  let O := axisRectangle 1 b l r ∩ {q | q.1 * saddleFactor q ≠ 0}
  have hoO : IsOpen O := hoR.inter (isOpen_ne_fun
    (continuous_fst.mul saddleFactor_regular.1.continuous) continuous_const)
  have hQ : MemSobolevLocOn 2 O (fun q ↦ V q / ((q.1 * saddleFactor q : ℝ) : ℂ)) :=
    (hV.memSobolevLocOn.mono inter_subset_left).div_smooth hoO
      (contDiff_fst.mul saddleFactor_regular.1) (fun _ hq ↦ hq.2)
  apply patch_of_comp hm
  refine ⟨O, hoO, ⟨htR, hb⟩, ?_⟩
  apply hQ.congr_ae_on
  have hid' := ae_restrict_of_ae_restrict_of_subset
    (inter_subset_left (t := {q | q.1 * saddleFactor q ≠ 0})) hid
  have hn := hm.quasiMeasurePreserving.ae ae_dipole_ne_zero
  filter_upwards [(ae_restrict_iff' hoO.measurableSet).mp hid', hn] with q hq hn _hq
  have hn' : (dipoleLift (planeAffine A c q) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  have hq' := hq _hq
  change f (planeAffine A c q) = (q.2 : ℂ) * V q at hq'
  change V q / ((q.1 * saddleFactor q : ℝ) : ℂ) = f (planeAffine A c q) /
    (dipoleLift (planeAffine A c q) : ℂ)
  have hv : (q.2 : ℂ) ≠ 0 := by
    intro hz
    apply hn'
    rw [hfac]
    push_cast
    rw [hz, zero_mul]
  rw [hq', hfac]
  push_cast
  exact (mul_div_mul_left (V q) ((q.1 : ℂ) * saddleFactor q) hv).symm

private theorem regular_quotient_patch {lam : ℝ} (hlam : lam ≠ 0) {ζ : L2}
    (hζ : IsEigenSolution lam ζ) (hs : InSector false false ζ)
    {p : ℝ × ℝ} (hp : dipoleLift p = 0) (hpS : p ∉ saddleSet) :
    ∃ W, IsOpen W ∧ p ∈ W ∧ MemSobolevLocOn 2 W
      (fun q ↦ contStream ζ q / (dipoleLift q : ℂ)) := by
  obtain ⟨n, hn, e, t, hpt⟩ := separatrix_axis_chart hp
  let P : ℝ × ℝ := (0, n * Real.pi)
  have hP : P ∈ saddleSet := ⟨0, n, by simpa using hn, by simp [P]⟩
  let S : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    if e then ContinuousLinearEquiv.prodComm ℝ ℝ ℝ else ContinuousLinearEquiv.refl ℝ _
  let A := S.trans (saddleLinear P hP)
  have hT (q : ℝ × ℝ) : planeAffine A P q =
      saddleOrthoChart P (if e then q.swap else q) := by
    rw [← planeAffine_saddleLinear P hP]
    change saddleLinear P hP (S q) + P =
      saddleLinear P hP (if e then q.swap else q) + P
    congr 2
    cases e <;> rfl
  have hmSwap : MeasurePreserving (Prod.swap : (ℝ × ℝ) → ℝ × ℝ) := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume))
  have hmS : MeasurePreserving S := by
    cases e
    · exact MeasurePreserving.id volume
    · exact hmSwap
  have hm : MeasurePreserving (planeAffine A P) := by
    convert (measurePreserving_saddleChart hP).comp hmS using 1
    funext q
    cases e <;> simpa [S] using hT q
  have hfac (q : ℝ × ℝ) : dipoleLift (planeAffine A P q) = q.2 * (q.1 * saddleFactor q) := by
    rw [hT, saddle_dipole_factorization hP]
    cases e <;> simp [saddleFactor] <;> ring
  have hodd : ∀ᵐ q, contStream ζ (planeAffine A P (axisReflect 1 q)) =
      -contStream ζ (planeAffine A P q) := by
    simp_rw [hT]
    cases e
    · simpa using contStream_chart_parity hP hs 1
    · have hh := hmSwap.quasiMeasurePreserving.ae (contStream_chart_parity hP hs 0)
      simpa [axisReflect] using hh
  have heq : planeAffine A P (t, 0) = p := by
    rw [hT]
    cases e <;> simpa using hpt.symm
  have hb : t * saddleFactor (t, 0) ≠ 0 := by
    intro hbad
    apply hpS
    rw [hpt]
    exact bad_axis_point_is_saddle hn e hbad
  obtain ⟨U, hU, hcover, _, _, hψ⟩ := dd_separatrix_h1 hlam hζ hs
  have hf := hψ.comp_planeAffine A P hm
  have ht : (t, 0) ∈ planeAffine A P ⁻¹' U := by
    change planeAffine A P (t, 0) ∈ U
    rw [heq]
    exact hcover hp
  have hh := regular_quotient_in_chart hm (hU.preimage (planeAffine A P).continuous)
    hf hodd hfac ht hb
  simpa only [heq] using hh

/-! ### Gluing and periodic reconstruction -/

private theorem contStream_local_h2 (ζ : L2) :
    MemSobolevLocOn 2 univ (contStream ζ) := by
  intro V _ hc _
  exact (memSobolevOn_liftL2 (memSobolev_two_invLap ζ)
    (hc.isBounded.subset subset_closure)).congr_ae (streamLift_ae_eq_contStream ζ)

private theorem local_h2_stream_quotient {lam : ℝ} (hlam : lam ≠ 0) {ζ : L2}
    (hζ : IsEigenSolution lam ζ) (hs : InSector false false ζ) :
    MemSobolevLocOn 2 univ (fun p ↦ contStream ζ p / (dipoleLift p : ℂ)) := by
  apply memSobolevLocOn_of_locally
  intro p _
  by_cases hzero : dipoleLift p = 0
  · by_cases hP : p ∈ saddleSet
    · exact saddle_quotient_patch hlam hζ hs hP
    · exact regular_quotient_patch hlam hζ hs hzero hP
  · let U := {q | dipoleLift q ≠ 0}
    have hd : ContDiff ℝ ∞ dipoleLift := by unfold dipoleLift; fun_prop
    have ho : IsOpen U := isOpen_ne_fun hd.continuous continuous_const
    exact ⟨U, ho, hzero, ((contStream_local_h2 ζ).mono (subset_univ U)).div_smooth ho
      hd (fun _ hq ↦ hq)⟩

/-- Construct global H² quotient data from local weighted division and point removal.
Parity of the quotient is a separate algebraic consequence of the multiplication identity. -/
theorem exists_h2_stream_quotient {lam : ℝ} (hlam : lam ≠ 0) {ζ : L2}
    (hζ : IsEigenSolution lam ζ) (hs : InSector false false ζ) :
    ∃ φ : L2, MemSobolev 2 φ ∧ ∀ᵐ t, invLap ζ t = (Ψ t : ℂ) * φ t := by
  have hp : IsPeriodicLift (fun p ↦ contStream ζ p / (dipoleLift p : ℂ)) := by
    intro p
    simp only [← Ψ_torusProj, contStream, torusProj, Real.Angle.coe_add,
      Real.Angle.coe_two_pi, add_zero, and_self]
  obtain ⟨φ, hφ, hlift⟩ := exists_memSobolev_of_periodic_lift hp
    (local_h2_stream_quotient hlam hζ hs)
  refine ⟨φ, hφ, ?_⟩
  have heq : contStream ζ = fun p ↦ (dipoleLift p : ℂ) *
      continuousRep φ (torusProj p) := by
    apply Measure.eq_of_ae_eq (μ := volume) _ (continuous_contStream ζ)
      ((by unfold dipoleLift; fun_prop : Continuous fun p ↦ (dipoleLift p : ℂ)).mul
        ((continuousRep φ).continuous.comp isOpenQuotientMap_torusProj.continuous))
    filter_upwards [hlift, ae_torusProj (coeFn_eq_continuousRep hφ),
      ae_dipole_ne_zero] with p hp hrep hn
    change φ (torusProj p) = _ at hp
    change contStream ζ p = (dipoleLift p : ℂ) * continuousRep φ (torusProj p)
    rw [← hrep, hp]
    exact (mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hn)).symm
  filter_upwards [coeFn_invLap_eq_continuousRep ζ, coeFn_eq_continuousRep hφ] with t ht hφt
  rw [ht, hφt]
  obtain ⟨p, rfl⟩ := torusProj_surjective t
  simpa only [contStream, Ψ_torusProj] using congrFun heq p

end NoEmbeddedEigenvalues
