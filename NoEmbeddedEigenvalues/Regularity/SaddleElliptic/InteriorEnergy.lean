module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.WeakJetOperations
public import NoEmbeddedEigenvalues.Geometry.Cells.LiftIntegration

/-! # Local energy estimates for Poisson equations -/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Complex
open scoped ContDiff ComplexConjugate

/-- The Cartesian Laplacian on a smooth complex-valued function. -/
def energyLaplacian (g : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  coordPartial 0 (coordPartial 0 g) p + coordPartial 1 (coordPartial 1 g) p

private theorem coordPartial_conj (j : Fin 2) {g : ℝ × ℝ → ℂ} (hg : Differentiable ℝ g) :
    coordPartial j (fun p ↦ conj (g p)) = fun p ↦ conj (coordPartial j g p) := by
  funext p
  fin_cases j
  · exact partialX_conj (hg p)
  · exact partialY_conj (hg p)

private theorem energy_scalar {a m x y z h k : ℝ} (ha : a ∈ Icc 0 1)
    (hm : 0 ≤ m) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hh : 0 ≤ h) (hk : 0 ≤ k) (t : ℝ) (ht : t = x ∨ t = y) :
    2 * (a * x) * (m * z) + 2 * (a * y) * (m * z) + h * a ^ 2 * z +
      k * (2 * a * (m * z) + a * (a * t)) ≤
      ((a * x) ^ 2 + (a * y) ^ 2) / 2 + 20 * (1 + m ^ 2) * (z ^ 2 + h ^ 2 + k ^ 2) := by
  have ha₀ := ha.1
  have ha₁ := ha.2
  have ht₀ : 0 ≤ t := ht.elim (fun ht ↦ ht ▸ hx) (fun ht ↦ ht ▸ hy)
  have hh' : h * a ^ 2 * z ≤ h * z := by
    have h₁ : a ^ 2 ≤ 1 := by simpa using (sq_le_sq₀ ha₀ zero_le_one).2 ha₁
    calc _ ≤ h * 1 * z := by gcongr
         _ = _ := by ring
  have hk' : k * (2 * a * (m * z) + a * (a * t)) ≤ k * (2 * (m * z) + a * t) := by
    calc _ ≤ k * (2 * 1 * (m * z) + 1 * (a * t)) := by gcongr
         _ = _ := by ring
  have hs : (a * t) ^ 2 ≤ (a * x) ^ 2 + (a * y) ^ 2 := by
    rcases ht with ht | ht
    · rw [ht]; exact le_add_of_nonneg_right (sq_nonneg _)
    · rw [ht]; exact le_add_of_nonneg_left (sq_nonneg _)
  nlinarith only [hh', hk', hs, sq_nonneg (a * x / 2 - 2 * m * z),
    sq_nonneg (a * y / 2 - 2 * m * z), sq_nonneg (h - z), sq_nonneg (k - m * z),
    sq_nonneg (a * t / 2 - k), sq_nonneg h, sq_nonneg k, sq_nonneg z,
    mul_nonneg (sq_nonneg m) (sq_nonneg h), mul_nonneg (sq_nonneg m) (sq_nonneg k),
    mul_nonneg (sq_nonneg m) (sq_nonneg z)]

/-- A real cutoff gives an interior gradient estimate for a smooth equation with either
an `L²` source or an `L²` source differentiated in one coordinate. -/
theorem smooth_interior_energy {A B : Set (ℝ × ℝ)} (hAB : A ⊆ B) (hAm : MeasurableSet A)
    (hBm : MeasurableSet B) (hBc : IsCompact (closure B))
    {η : ℝ × ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηB : tsupport η ⊆ B) (hηA : ∀ p ∈ A, η p = 1) (hη01 : ∀ p, η p ∈ Icc 0 1)
    {M : ℝ} (hM : 0 ≤ M) (hMd : ∀ j p, ‖coordPartial j (fun q ↦ (η q : ℂ)) p‖ ≤ M)
    {g h k : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (hk : ContDiff ℝ ∞ k)
    (i : Fin 2) (hP : ∀ p ∈ B, energyLaplacian g p = h p + coordPartial i k p) :
    (∫ p in A, ‖coordPartial 0 g p‖ ^ 2 + ‖coordPartial 1 g p‖ ^ 2) ≤
      40 * (1 + M ^ 2) * ∫ p in B, ‖g p‖ ^ 2 + ‖h p‖ ^ 2 + ‖k p‖ ^ 2 := by
  let a : ℝ × ℝ → ℂ := fun p ↦ η p
  have ha : ContDiff ℝ ∞ a := Complex.ofRealCLM.contDiff.comp hη
  have hac : HasCompactSupport a := hηc.comp_left Complex.ofReal_zero
  let ψ : ℝ × ℝ → ℂ := fun p ↦ a p * a p * conj (g p)
  have hψ : ContDiff ℝ ∞ ψ := (ha.mul ha).mul (contDiff_conj hg)
  have hψc : HasCompactSupport ψ := hac.mul_right.mul_right
  have hψa : tsupport ψ ⊆ tsupport a := tsupport_mul_subset_left.trans tsupport_mul_subset_left
  have hψB : tsupport ψ ⊆ B := hψa.trans
    ((tsupport_comp_subset Complex.ofReal_zero η).trans hηB)
  let d := fun j ↦ coordPartial j g
  let P : ℝ × ℝ → ℂ := fun p ↦ d 0 p * coordPartial 0 ψ p + d 1 p * coordPartial 1 ψ p +
    h p * ψ p - k p * coordPartial i ψ p
  let Q : ℝ × ℝ → ℝ := fun p ↦ (η p * ‖d 0 p‖) ^ 2 + (η p * ‖d 1 p‖) ^ 2
  let L : ℝ × ℝ → ℝ := fun p ↦ ‖g p‖ ^ 2 + ‖h p‖ ^ 2 + ‖k p‖ ^ 2
  have hψdc (j : Fin 2) : HasCompactSupport (coordPartial j ψ) :=
    hψc.of_isClosed_subset (isClosed_tsupport _) (tsupport_coordPartial_subset j ψ)
  have hψdcB (j : Fin 2) : tsupport (coordPartial j ψ) ⊆ B :=
    (tsupport_coordPartial_subset j ψ).trans hψB
  have hψdiff (j : Fin 2) := contDiff_coordPartial_top j hψ
  have hd (j : Fin 2) := contDiff_coordPartial_top j hg
  have hQ (p : ℝ × ℝ) : 0 ≤ Q p := by dsimp [Q]; positivity
  have hLc : Continuous L := ((hg.continuous.norm.pow 2).add (hh.continuous.norm.pow 2)).add
    (hk.continuous.norm.pow 2)
  have hLi : IntegrableOn L B :=
    (hLc.continuousOn.integrableOn_compact hBc).mono_set subset_closure
  have hQc : Continuous Q :=
    ((hη.continuous.mul (hd 0).continuous.norm).pow 2).add
      ((hη.continuous.mul (hd 1).continuous.norm).pow 2)
  have hQi : IntegrableOn Q B :=
    (hQc.continuousOn.integrableOn_compact hBc).mono_set subset_closure
  have hPic (j : Fin 2) : Integrable (fun p ↦ d j p * coordPartial j ψ p) :=
    ((hd j).continuous.mul (hψdiff j).continuous).integrable_of_hasCompactSupport (hψdc j).mul_left
  have hPi₀ : Integrable (fun p ↦ h p * ψ p) :=
    (hh.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hψc.mul_left
  have hPi₁ : Integrable (fun p ↦ k p * coordPartial i ψ p) :=
    (hk.continuous.mul (hψdiff i).continuous).integrable_of_hasCompactSupport (hψdc i).mul_left
  have hPi : Integrable P := ((hPic 0).add (hPic 1) |>.add hPi₀).sub hPi₁
  have hIntP : ∫ p, P p = 0 := by
    have hIb (j : Fin 2) := integral_mul_coordPartial j ((hd j).of_le (by simp))
      (hψ.of_le (by simp)) hψc
    have hIk := integral_mul_coordPartial i (hk.of_le (by simp)) (hψ.of_le (by simp)) hψc
    have hL (j : Fin 2) : Integrable (fun p ↦ coordPartial j (d j) p * ψ p) :=
      ((contDiff_coordPartial_top j (hd j)).continuous.mul hψ.continuous)
        |>.integrable_of_hasCompactSupport hψc.mul_left
    have hK : Integrable (fun p ↦ coordPartial i k p * ψ p) :=
      ((contDiff_coordPartial_top i hk).continuous.mul hψ.continuous)
        |>.integrable_of_hasCompactSupport hψc.mul_left
    have hI : (∫ p, (energyLaplacian g p - (h p + coordPartial i k p)) * ψ p) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with p
      change (energyLaplacian g p - (h p + coordPartial i k p)) * ψ p = 0
      by_cases hp : p ∈ tsupport ψ
      · rw [hP p (hψB hp), sub_self, zero_mul]
      · rw [image_eq_zero_of_notMem_tsupport hp, mul_zero]
    change (∫ p, (coordPartial 0 (d 0) p + coordPartial 1 (d 1) p -
      (h p + coordPartial i k p)) * ψ p) = 0 at hI
    simp only [sub_mul, add_mul] at hI
    have hI' := integral_sub ((hL 0).add (hL 1)) (hPi₀.add hK)
    simp only [Pi.add_apply] at hI'
    rw [hI, integral_add (hL 0) (hL 1), integral_add hPi₀ hK] at hI'
    have hEq := integral_sub ((hPic 0).add (hPic 1) |>.add hPi₀) hPi₁
    change ∫ p, P p = _ at hEq
    rw [hEq]
    simp only [Pi.add_apply]
    have hEq' := integral_add ((hPic 0).add (hPic 1)) hPi₀
    simp only [Pi.add_apply] at hEq'
    rw [hEq', integral_add (hPic 0) (hPic 1)]
    dsimp only [d]
    rw [hIb 0, hIb 1, hIk]
    linear_combination hI'
  have hIntPB : ∫ p in B, (P p).re = 0 := by
    have he : (∫ p in B, (P p).re) = ∫ p, (P p).re := by
      rw [← integral_indicator hBm]
      congr 1
      funext p
      by_cases hp : p ∈ B
      · exact indicator_of_mem hp _
      · have h₁ : ψ p = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hp (hψB h)
        have h₂ (j : Fin 2) : coordPartial j ψ p = 0 :=
          image_eq_zero_of_notMem_tsupport fun h ↦ hp (hψdcB j h)
        simp [hp, P, h₁, h₂]
    rw [he]
    change (∫ p, RCLike.re (P p)) = 0
    rw [integral_re hPi, hIntP, RCLike.zero_re]
  have hchain (j : Fin 2) (p : ℝ × ℝ) : coordPartial j ψ p =
      2 * a p * coordPartial j a p * conj (g p) + a p * a p * conj (d j p) := by
    have had := ha.differentiable (by simp)
    have hgd := hg.differentiable (by simp)
    have hcg : Differentiable ℝ (fun q ↦ conj (g q)) := Complex.differentiable_conj.comp hgd
    have haa : Differentiable ℝ (fun q ↦ a q * a q) := had.mul had
    change coordPartial j (fun q ↦ (a q * a q) * conj (g q)) p = _
    rw [coordPartial_mul j haa hcg, coordPartial_mul j had had, coordPartial_conj j hgd]
    dsimp [d]
    ring
  have hnorm (p : ℝ × ℝ) : ‖a p‖ = η p := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hη01 p).1]
  have hpwise (p : ℝ × ℝ) : Q p / 2 ≤ (P p).re + 20 * (1 + M ^ 2) * L p := by
    let T (j : Fin 2) := 2 * a p * coordPartial j a p * conj (g p)
    have hT (j : Fin 2) : ‖T j‖ ≤ 2 * η p * (M * ‖g p‖) := by
      dsimp [T]
      rw [norm_mul, norm_mul, norm_mul, norm_ofNat, hnorm, Complex.norm_conj]
      have := (hη01 p).1
      calc _ ≤ 2 * η p * M * ‖g p‖ := by gcongr; exact hMd j p
           _ = _ := by ring
    have hψ₁ : ‖ψ p‖ = η p ^ 2 * ‖g p‖ := by
      simp only [ψ, norm_mul, hnorm, Complex.norm_conj, pow_two]
    have hψ₂ : ‖coordPartial i ψ p‖ ≤ 2 * η p * (M * ‖g p‖) + η p * (η p * ‖d i p‖) := by
      rw [hchain]
      refine (norm_add_le _ _).trans (add_le_add (hT i) ?_)
      rw [norm_mul, norm_mul, hnorm, Complex.norm_conj, mul_assoc]
    have hr (j : Fin 2) : (d j p * coordPartial j ψ p).re =
        (η p * ‖d j p‖) ^ 2 + (d j p * T j).re := by
      rw [hchain, mul_add, Complex.add_re, add_comm]
      congr 1
      rw [show d j p * (a p * a p * conj (d j p)) = a p * a p * (d j p * conj (d j p)) by ring,
        Complex.mul_conj]
      simp [a, pow_two, Complex.normSq_eq_norm_sq, mul_assoc, mul_left_comm, mul_comm]
    have hab := (hη01 p).1
    have hlow (j : Fin 2) : -(d j p * T j).re ≤ 2 * (η p * ‖d j p‖) * (M * ‖g p‖) := by
      calc
        _ ≤ ‖d j p * T j‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
        _ ≤ ‖d j p‖ * (2 * η p * (M * ‖g p‖)) := by rw [norm_mul]; gcongr; exact hT j
        _ = _ := by ring
    have hl₀ : -(h p * ψ p).re ≤ ‖h p‖ * η p ^ 2 * ‖g p‖ := by
      calc
        _ ≤ ‖h p * ψ p‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
        _ = _ := by rw [norm_mul, hψ₁, mul_assoc]
    have hl₁ : (k p * coordPartial i ψ p).re ≤
        ‖k p‖ * (2 * η p * (M * ‖g p‖) + η p * (η p * ‖d i p‖)) := by
      calc
        _ ≤ ‖k p * coordPartial i ψ p‖ := Complex.re_le_norm _
        _ ≤ _ := by rw [norm_mul]; gcongr
    have hs := energy_scalar (hη01 p) hM (norm_nonneg (d 0 p)) (norm_nonneg (d 1 p))
      (norm_nonneg (g p)) (norm_nonneg (h p)) (norm_nonneg (k p)) ‖d i p‖
      (by fin_cases i <;> simp)
    simp only [P, Q, L, Complex.sub_re, Complex.add_re, hr]
    linarith only [hs, hlow 0, hlow 1, hl₀, hl₁]
  have hPre : IntegrableOn (fun p ↦ (P p).re) B := hPi.re.integrableOn
  have hInt := integral_mono (hQi.div_const 2)
    (hPre.add (hLi.const_mul (20 * (1 + M ^ 2)))) hpwise
  have hI₂ := integral_add hPre (hLi.const_mul (20 * (1 + M ^ 2)))
  simp only [Pi.add_apply] at hInt
  rw [integral_div, hI₂, hIntPB, zero_add, integral_const_mul] at hInt
  have hIntA : (∫ p in A, ‖d 0 p‖ ^ 2 + ‖d 1 p‖ ^ 2) ≤ ∫ p in B, Q p := by
    refine (setIntegral_congr_fun hAm (fun p hp ↦ ?_)).le.trans
      (setIntegral_mono_set hQi (Eventually.of_forall hQ) (Eventually.of_forall hAB))
    simp [Q, hηA p hp]
  linarith


private theorem coordPartial_swap (i j : Fin 2) {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    coordPartial i (coordPartial j f) = coordPartial j (coordPartial i f) := by
  have h := funext (partialY_partialX (hf.of_le (by simp)))
  fin_cases i <;> fin_cases j <;> simp [coordPartial, h]

/-- Coordinate differentiation of a pointwise sum. -/
theorem coordPartial_sum (i : Fin 2) {g h : ℝ × ℝ → ℂ}
    (hg : Differentiable ℝ g) (hh : Differentiable ℝ h) :
    coordPartial i (fun p ↦ g p + h p) =
      fun p ↦ coordPartial i g p + coordPartial i h p := by
  funext p
  fin_cases i
  · exact partialX_add (hg p) (hh p)
  · exact partialY_add (hg p) (hh p)

private theorem coordPartial_energyLaplacian (i : Fin 2) {f : ℝ × ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) :
    energyLaplacian (coordPartial i f) = coordPartial i (energyLaplacian f) := by
  have hh (j : Fin 2) := contDiff_coordPartial_top j (contDiff_coordPartial_top j hf)
  unfold energyLaplacian
  rw [coordPartial_sum i ((hh 0).differentiable (by simp)) ((hh 1).differentiable (by simp))]
  simp only [coordPartial_swap 0 i hf, coordPartial_swap 1 i hf,
    coordPartial_swap 0 i (contDiff_coordPartial_top 0 hf),
    coordPartial_swap 1 i (contDiff_coordPartial_top 1 hf)]

/-- Energy of a single complex-valued function on a patch. -/
def squareEnergy (U : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℂ) : ℝ :=
  ∫ p in U, ‖f p‖ ^ 2

theorem squareEnergy_nonneg (U : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℂ) :
    0 ≤ squareEnergy U f := integral_nonneg fun _ ↦ sq_nonneg _

private theorem energyIntegrable {f : ℝ × ℝ → ℂ} {U : Set (ℝ × ℝ)} (hf : Continuous f)
    (hc : IsCompact (closure U)) : IntegrableOn (fun p ↦ ‖f p‖ ^ 2) U :=
  ((hf.norm.pow 2).continuousOn.integrableOn_compact hc).mono_set subset_closure

private theorem exists_interior_gradient_estimate {A B : Set (ℝ × ℝ)} (hA : IsOpen A)
    (hB : IsOpen B) (hAc : IsCompact (closure A)) (hBc : IsCompact (closure B))
    (hAB : closure A ⊆ B) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {g h k : ℝ × ℝ → ℂ}, ContDiff ℝ ∞ g → ContDiff ℝ ∞ h →
      ContDiff ℝ ∞ k → ∀ i, (∀ p ∈ B, energyLaplacian g p = h p + coordPartial i k p) →
      ∀ j, squareEnergy A (coordPartial j g) ≤
        K * (squareEnergy B g + squareEnergy B h + squareEnergy B k) := by
  obtain ⟨V, hVo, hAV, hVB, hVc⟩ := exists_open_between_and_isCompact_closure hAc hB hAB
  obtain ⟨η, hη, hη01, hηs, hηeq⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hVo isClosed_closure hAV
  have hc : HasCompactSupport η := by rwa [HasCompactSupport, tsupport, hηs]
  have hs : tsupport η ⊆ B := by rwa [tsupport, hηs]
  have hηC : ContDiff ℝ ∞ (fun q ↦ (η q : ℂ)) := Complex.ofRealCLM.contDiff.comp hη
  have hηcs := hc.comp_left Complex.ofReal_zero
  have hBd (j : Fin 2) := (contDiff_coordPartial_top j hηC).continuous
    |>.bounded_above_of_compact_support
      (hηcs.of_isClosed_subset (isClosed_tsupport _) (tsupport_coordPartial_subset j _))
  obtain ⟨M₀, hM₀⟩ := hBd 0
  obtain ⟨M₁, hM₁⟩ := hBd 1
  let M := max 0 (max M₀ M₁)
  have hMd (j : Fin 2) (p : ℝ × ℝ) : ‖coordPartial j (fun q ↦ (η q : ℂ)) p‖ ≤ M := by
    fin_cases j
    · exact (hM₀ p).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (hM₁ p).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨40 * (1 + M ^ 2), by nlinarith [sq_nonneg M], ?_⟩
  intro g h k hg hh hk i hp j
  have he := smooth_interior_energy (subset_closure.trans hAB) hA.measurableSet hB.measurableSet
    hBc hη hc hs (fun p hp ↦ (hηeq p).mp (subset_closure hp))
    (fun p ↦ hη01 (mem_range_self p)) (le_max_left _ _) hMd hg hh hk i hp
  have hd (j : Fin 2) := energyIntegrable (contDiff_coordPartial_top j hg).continuous hAc
  have hsum := integral_add ((energyIntegrable hg.continuous hBc).add
    (energyIntegrable hh.continuous hBc)) (energyIntegrable hk.continuous hBc)
  simp only [Pi.add_apply] at hsum
  rw [integral_add (hd 0) (hd 1), hsum,
    integral_add (energyIntegrable hg.continuous hBc) (energyIntegrable hh.continuous hBc)] at he
  change squareEnergy A (coordPartial 0 g) + squareEnergy A (coordPartial 1 g) ≤ _ at he
  fin_cases j
  · exact (le_add_of_nonneg_right (squareEnergy_nonneg _ _)).trans he
  · exact (le_add_of_nonneg_left (squareEnergy_nonneg _ _)).trans he

/-- Three interior gradient bounds control the third derivatives of a smooth function. -/
theorem smooth_interior_third_estimate {A B : Set (ℝ × ℝ)} (hA : IsOpen A) (hB : IsOpen B)
    (hAc : IsCompact (closure A)) (hBc : IsCompact (closure B)) (hAB : closure A ⊆ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ {v : ℝ × ℝ → ℂ}, ContDiff ℝ ∞ v →
      ∀ i j k : Fin 2, squareEnergy A (coordPartial i (coordPartial j (coordPartial k v))) ≤
        C * (squareEnergy B v + squareEnergy B (energyLaplacian v) +
          squareEnergy B (coordPartial k (energyLaplacian v))) := by
  obtain ⟨B₂, hB₂, hAB₂, hB₂B, hB₂c⟩ := exists_open_between_and_isCompact_closure hAc hB hAB
  obtain ⟨B₁, hB₁, hAB₁, hB₁B₂, hB₁c⟩ := exists_open_between_and_isCompact_closure hAc hB₂ hAB₂
  obtain ⟨K₁, hK₁, h₁⟩ := exists_interior_gradient_estimate hB₂ hB hB₂c hBc hB₂B
  obtain ⟨K₂, hK₂, h₂⟩ := exists_interior_gradient_estimate hB₁ hB₂ hB₁c hB₂c hB₁B₂
  obtain ⟨K₃, hK₃, h₃⟩ := exists_interior_gradient_estimate hA hB₁ hAc hB₁c hAB₁
  have hp₁ : 0 < K₁ := zero_lt_one.trans_le hK₁
  have hp₂ : 0 < K₂ := zero_lt_one.trans_le hK₂
  have hp₃ : 0 < K₃ := zero_lt_one.trans_le hK₃
  refine ⟨K₃ * (K₂ * (K₁ + 1) + 1), by positivity, ?_⟩
  intro v hv i j k
  let H := energyLaplacian v
  have hd (j : Fin 2) := contDiff_coordPartial_top j hv
  have hH : ContDiff ℝ ∞ H := (contDiff_coordPartial_top 0 (hd 0)).add
    (contDiff_coordPartial_top 1 (hd 1))
  have hdc : ∀ j, coordPartial j (fun _ : ℝ × ℝ ↦ (0 : ℂ)) = 0 := by
    intro j
    funext p
    fin_cases j <;> simp [coordPartial, partialX, partialY]
  have hz (U : Set (ℝ × ℝ)) : squareEnergy U (fun _ ↦ 0) = 0 := by simp [squareEnergy]
  have e₁ := h₁ hv hH (contDiff_const (c := (0 : ℂ))) 0
    (fun p _ ↦ by change H p = H p + _; rw [hdc]; simp) k
  have e₂ := h₂ (hd k) (contDiff_const (c := (0 : ℂ))) hH k
    (fun p _ ↦ by rw [coordPartial_energyLaplacian k hv]; simp [H]) j
  have e₃ := h₃ (contDiff_coordPartial_top j (hd k)) (contDiff_const (c := (0 : ℂ)))
    (contDiff_coordPartial_top k hH) j
    (fun p _ ↦ by
      rw [coordPartial_energyLaplacian j (hd k), coordPartial_energyLaplacian k hv]
      simp [H]) i
  simp only [hz, add_zero] at e₁ e₂ e₃
  have hmono {S : Set (ℝ × ℝ)} (hSB : S ⊆ B) {f : ℝ × ℝ → ℂ} (hf : Continuous f) :
      squareEnergy S f ≤ squareEnergy B f :=
    setIntegral_mono_set (energyIntegrable hf hBc) (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (Eventually.of_forall hSB)
  have h₂B := subset_closure.trans hB₂B
  let X := squareEnergy B v + squareEnergy B H + squareEnergy B (coordPartial k H)
  have hXg : squareEnergy B v + squareEnergy B H ≤ X :=
    le_add_of_nonneg_right (squareEnergy_nonneg _ _)
  have hXH : squareEnergy B₂ H ≤ X :=
    (hmono h₂B hH.continuous).trans (by
      dsimp only [X]
      linarith only [squareEnergy_nonneg B v, squareEnergy_nonneg B (coordPartial k H)])
  have hXd : squareEnergy B₁ (coordPartial k H) ≤ X :=
    (hmono (subset_closure.trans (hB₁B₂.trans h₂B))
      (contDiff_coordPartial_top k hH).continuous).trans (by
        dsimp only [X]
        linarith only [squareEnergy_nonneg B v, squareEnergy_nonneg B H])
  have e₁' := e₁.trans (mul_le_mul_of_nonneg_left hXg hp₁.le)
  have e₂' := e₂.trans (mul_le_mul_of_nonneg_left (add_le_add e₁' hXH) hp₂.le)
  have e₃' := e₃.trans (mul_le_mul_of_nonneg_left (add_le_add e₂' hXd) hp₃.le)
  convert e₃' using 1
  ring

end NoEmbeddedEigenvalues
