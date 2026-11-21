module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.EvenGradientHardy
public import NoEmbeddedEigenvalues.OddOdd.Picone.OddOddPiconeIntegrability

/-!
# Integrability of the original and divided odd–odd gradient energies

Diagonal Hardy division controls the singular normal coefficient. The ground
state has bounded cosine-divided diagonal derivatives, so subtracting its
logarithmic gradient preserves the same integrability class.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Topology Real

/-- The singular normal coefficient is dominated by the diagonal Hardy densities. -/
theorem ddMatrixForm_diagonal_bound {p : ℝ × ℝ} (hp : p ∈ cellSquare)
    (hr : gradSq dipoleLift p ≠ 0) (vx vy : ℂ) :
    |ddMatrixForm p vx vy| ≤ 64 * (‖vx‖ ^ 2 + ‖vy‖ ^ 2 +
      ‖(vx + vy) / (cos (diagCoord p).1 : ℂ)‖ ^ 2 +
      ‖(vx - vy) / (cos (diagCoord p).2 : ℂ)‖ ^ 2) := by
  let s := dipoleLift p
  let r := gradSq dipoleLift p
  let a := (diagCoord p).1
  let b := (diagCoord p).2
  let A := (vx + vy) / (cos a : ℂ)
  let B := (vx - vy) / (cos b : ℂ)
  let N := normalDeriv (fun _ ↦ vx) (fun _ ↦ vy) p
  let T := tangentDeriv (fun _ ↦ vx) (fun _ ↦ vy) p
  have hs : 0 < s := by
    simpa [s, positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
  have hrp : 0 < r := lt_of_le_of_ne (by dsimp [r]; rw [gradSq_dipoleLift]; positivity) hr.symm
  have ha : 0 < cos a := cos_pos_of_mem_Ioo (by
    exact ⟨(abs_lt.mp hp.1).1, (abs_lt.mp hp.1).2⟩)
  have hb : 0 < cos b := cos_pos_of_mem_Ioo (by
    exact ⟨(abs_lt.mp hp.2).1, (abs_lt.mp hp.2).2⟩)
  have hρ : gradNorm p ^ 2 = r := by
    dsimp [gradNorm, r]
    rw [sq_sqrt (by positivity), gradSq_dipoleLift]
  have hf : ‖N‖ ^ 2 + ‖T‖ ^ 2 = ‖vx‖ ^ 2 + ‖vy‖ ^ 2 :=
    norm_normalDeriv_sq_add_norm_tangentDeriv_sq _ _ (by nlinarith [sq_nonneg (gradNorm p)])
  obtain ⟨-, hA, hC⟩ := dd_coefficients_bound (p := p) (a := s / 2)
    (by positivity) (by dsimp [s]; linarith)
  have hAb : |ddA p| ≤ 8 + 32 / s := by convert hA using 1; field_simp; ring
  have hbase : |ddMatrixForm p vx vy| ≤ |ddA p| * ‖N‖ ^ 2 + 4 * ‖T‖ ^ 2 := by
    calc _ ≤ |ddA p * ‖N‖ ^ 2| + |ddC p * ‖T‖ ^ 2| := abs_add_le _ _
         _ ≤ _ := by rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ‖N‖),
                      abs_of_nonneg (sq_nonneg ‖T‖)]; gcongr
  by_cases hs1 : 1 ≤ s
  · have hh : |ddA p| ≤ 40 := hAb.trans (by
      have hd : 32 / s ≤ 32 := (div_le_iff₀ hs).mpr (by linarith)
      linarith)
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖N‖)
    change |ddMatrixForm p vx vy| ≤ 64 * (‖vx‖ ^ 2 + ‖vy‖ ^ 2 + ‖A‖ ^ 2 + ‖B‖ ^ 2)
    nlinarith [sq_nonneg ‖T‖, sq_nonneg ‖vx‖, sq_nonneg ‖vy‖,
      sq_nonneg ‖(vx + vy) / (cos a : ℂ)‖, sq_nonneg ‖(vx - vy) / (cos b : ℂ)‖]
  · have hrs : s ≤ r := by
      have hm := dipoleLift_mul_le_gradSq p
      change s * (2 - s) ≤ r at hm
      nlinarith [sq_nonneg s, hs1]
    have hx : p.1 = a + b := by dsimp [a, b, diagCoord]; ring
    have hy : p.2 = a - b := by dsimp [a, b, diagCoord]; ring
    have hprod : s = 2 * cos a * cos b := dipoleLift_eq_diag p
    have he : (sin p.1 : ℂ) * vx + (sin p.2 : ℂ) * vy =
        (s / 2 : ℝ) * ((sin a : ℂ) * A + (sin b : ℂ) * B) := by
      rw [hx, hy, sin_add, sin_sub, hprod]
      dsimp [A, B]
      have haC : (cos a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
      have hbC : (cos b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
      simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div]
      field_simp
      ring
    have hterms : ‖(sin a : ℂ) * A + (sin b : ℂ) * B‖ ^ 2 ≤
        2 * (‖A‖ ^ 2 + ‖B‖ ^ 2) := by
      have bound (t : ℝ) (z : ℂ) : ‖(sin t : ℂ) * z‖ ≤ ‖z‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (abs_sin_le_one _)
      have hh := (norm_add_le ((sin a : ℂ) * A) ((sin b : ℂ) * B)).trans
        (add_le_add (bound a A) (bound b B))
      have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hh
      nlinarith [sq_nonneg (‖A‖ - ‖B‖)]
    have hnr : ‖N‖ ^ 2 * r = ‖(sin p.1 : ℂ) * vx + (sin p.2 : ℂ) * vy‖ ^ 2 := by
      dsimp [N, normalDeriv]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs, hρ]
      exact div_mul_cancel₀ _ hr
    have hn : ‖N‖ ^ 2 ≤ s / 2 * (‖A‖ ^ 2 + ‖B‖ ^ 2) := by
      have hh : ‖N‖ ^ 2 * r ≤ s ^ 2 / 2 * (‖A‖ ^ 2 + ‖B‖ ^ 2) := by
        rw [hnr, he, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
        have hh := mul_le_mul_of_nonneg_left hterms (sq_nonneg (s / 2))
        nlinarith
      apply (mul_le_mul_iff_right₀ hs).mp
      nlinarith [mul_le_mul_of_nonneg_left hrs (sq_nonneg ‖N‖)]
    have hh : |ddA p| * ‖N‖ ^ 2 ≤ 20 * (‖A‖ ^ 2 + ‖B‖ ^ 2) := by
      calc _ ≤ (8 + 32 / s) * ‖N‖ ^ 2 := mul_le_mul_of_nonneg_right hAb (sq_nonneg _)
           _ ≤ (8 + 32 / s) * (s / 2 * (‖A‖ ^ 2 + ‖B‖ ^ 2)) :=
             mul_le_mul_of_nonneg_left hn (by positivity)
           _ = (4 * s + 16) * (‖A‖ ^ 2 + ‖B‖ ^ 2) := by field_simp; ring
           _ ≤ _ := by gcongr; linarith
    change |ddMatrixForm p vx vy| ≤ 64 * (‖vx‖ ^ 2 + ‖vy‖ ^ 2 + ‖A‖ ^ 2 + ‖B‖ ^ 2)
    nlinarith [sq_nonneg ‖A‖, sq_nonneg ‖B‖, sq_nonneg ‖N‖]

private theorem ae_regular_cell :
    ∀ᵐ p ∂volume.restrict cellSquare, p ∈ cellSquare ∧ gradSq dipoleLift p ≠ 0 := by
  filter_upwards [ae_restrict_mem isOpen_cellSquare.measurableSet,
    ae_restrict_of_ae ae_cos_fst_ne_cos_snd] with p hp hn
  have hs : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp
  have ht : dipoleLift p < 2 := by
    by_contra hge
    apply hn
    unfold dipoleLift at hge
    linarith [cos_le_one p.1, cos_le_one p.2]
  exact ⟨hp, (gradSq_dipoleLift_pos hs ht).ne'⟩

/-- A diagonal Hardy class suffices for absolute integrability of the matrix form. -/
theorem ddMatrixForm_integrable_of_diagonal {gx gy : ℝ × ℝ → ℂ}
    (hx : MemLp gx 2 (volume.restrict cellSquare))
    (hy : MemLp gy 2 (volume.restrict cellSquare))
    (ha : MemLp (fun p ↦ (gx p + gy p) / (cos (diagCoord p).1 : ℂ)) 2
      (volume.restrict cellSquare))
    (hb : MemLp (fun p ↦ (gx p - gy p) / (cos (diagCoord p).2 : ℂ)) 2
      (volume.restrict cellSquare)) :
    IntegrableOn (fun p ↦ ddMatrixForm p (gx p) (gy p)) cellSquare := by
  have hi := (((hx.norm.integrable_sq.add hy.norm.integrable_sq).add
    ha.norm.integrable_sq).add hb.norm.integrable_sq).const_mul 64
  have mx := hx.aestronglyMeasurable.aemeasurable
  have my := hy.aestronglyMeasurable.aemeasurable
  have hm : AEMeasurable (fun p ↦ ddMatrixForm p (gx p) (gy p))
      (volume.restrict cellSquare) := by
    unfold ddMatrixForm ddA ddC normalDeriv tangentDeriv gradNorm
    rw [gradSq_dipoleLift]
    unfold dipoleLift
    fun_prop
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_regular_cell] with p hp
  simpa only [Real.norm_eq_abs, Pi.add_apply] using
    ddMatrixForm_diagonal_bound hp.1 hp.2 (gx p) (gy p)

private def groundDiagonal (j : Fin 2) (p : ℝ × ℝ) : ℝ :=
  let a := (diagCoord p).1
  let b := (diagCoord p).2
  if j = 0 then -2 * sin a * (1 / 8 + groundLogCoeff (gradSq dipoleLift p) *
    (cos b ^ 2 - sin b ^ 2)) / ddGround p
  else -2 * sin b * (1 / 8 + groundLogCoeff (gradSq dipoleLift p) *
    (cos a ^ 2 - sin a ^ 2)) / ddGround p

private theorem measurable_groundDiagonal (j : Fin 2) : Measurable (groundDiagonal j) := by
  unfold groundDiagonal groundLogCoeff ddGround diagCoord
  rw [gradSq_dipoleLift]
  unfold dipoleLift
  split_ifs <;> fun_prop

private theorem groundDiagonal_bound (j : Fin 2) (p : ℝ × ℝ) :
    |groundDiagonal j p| ≤ 1 := by
  have hr : 0 ≤ gradSq dipoleLift p := by rw [gradSq_dipoleLift]; positivity
  have hr2 : gradSq dipoleLift p ≤ 2 := by
    rw [gradSq_dipoleLift]
    nlinarith [sin_sq_le_one p.1, sin_sq_le_one p.2]
  have hL := groundLogCoeff_bound hr hr2
  have hw := one_le_ddGround p
  have bound (a b : ℝ) :
      |-2 * sin a * (1 / 8 + groundLogCoeff (gradSq dipoleLift p) *
        (cos b ^ 2 - sin b ^ 2)) / ddGround p| ≤ 1 := by
    have hc : |cos b ^ 2 - sin b ^ 2| ≤ 1 := by
      rw [abs_le]
      constructor <;> nlinarith [sin_sq_add_cos_sq b, sq_nonneg (sin b), sq_nonneg (cos b)]
    have hs : |1 / 8 + groundLogCoeff (gradSq dipoleLift p) * (cos b ^ 2 - sin b ^ 2)| ≤
        1 / 4 := by
      calc _ ≤ |(1 / 8 : ℝ)| + |groundLogCoeff (gradSq dipoleLift p) *
           (cos b ^ 2 - sin b ^ 2)| := abs_add_le _ _
           _ ≤ 1 / 4 := by
             rw [abs_mul]
             norm_num only
             have hh := mul_le_mul hL hc (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 8)
             linarith
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (hw.trans' zero_le_one)]
    norm_num only
    apply (div_le_iff₀ (zero_lt_one.trans_le hw)).mpr
    have hh := mul_le_mul (abs_sin_le_one a) hs (abs_nonneg _) zero_le_one
    linarith
  unfold groundDiagonal
  split_ifs <;> exact bound _ _

private theorem groundDiagonal_eq {p : ℝ × ℝ} (hr : gradSq dipoleLift p ≠ 0) :
    cos (diagCoord p).1 * groundDiagonal 0 p =
      (partialX ddGround p + partialY ddGround p) / ddGround p ∧
    cos (diagCoord p).2 * groundDiagonal 1 p =
      (partialX ddGround p - partialY ddGround p) / ddGround p := by
  let a := (diagCoord p).1
  let b := (diagCoord p).2
  have hx : p.1 = a + b := by dsimp [a, b, diagCoord]; ring
  have hy : p.2 = a - b := by dsimp [a, b, diagCoord]; ring
  have hplus : partialX ddGround p + partialY ddGround p =
      -2 * sin a * cos a * (1 / 8 + groundLogCoeff (gradSq dipoleLift p) *
        (cos b ^ 2 - sin b ^ 2)) := by
    rw [partialX_ddGround hr, partialY_ddGround hr, hx, hy]
    simp only [sin_add, sin_sub, cos_add, cos_sub]
    linear_combination (-(sin a * cos a) / 4) * sin_sq_add_cos_sq b
  have hminus : partialX ddGround p - partialY ddGround p =
      -2 * sin b * cos b * (1 / 8 + groundLogCoeff (gradSq dipoleLift p) *
        (cos a ^ 2 - sin a ^ 2)) := by
    rw [partialX_ddGround hr, partialY_ddGround hr, hx, hy]
    simp only [sin_add, sin_sub, cos_add, cos_sub]
    linear_combination (-(sin b * cos b) / 4) * sin_sq_add_cos_sq a
  constructor
  · rw [hplus]
    simp only [groundDiagonal, ↓reduceIte]
    ring
  · rw [hminus]
    simp only [groundDiagonal, ite_eq_right (show (1 : Fin 2) ≠ 0 by decide)]
    ring

private theorem memLp_mul_real_bounded {f : ℝ × ℝ → ℂ} {c : ℝ × ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict cellSquare)) (hc : Measurable c)
    (hb : ∀ p, |c p| ≤ 1) :
    MemLp (fun p ↦ f p * (c p : ℂ)) 2 (volume.restrict cellSquare) := by
  apply hf.of_le_mul (c := 1)
    (hf.aestronglyMeasurable.mul (Complex.measurable_ofReal.comp hc).aestronglyMeasurable)
  exact Eventually.of_forall fun p ↦ by
    change ‖f p * (c p : ℂ)‖ ≤ 1 * ‖f p‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, one_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hb p)

/-- The even boundary Hardy estimate controls the original and divided gradient energies. -/
theorem dd_gradient_energies_integrable {φ dx dy : L2} (hφ : MemSobolev 2 φ)
    (hs : InSector true true φ) (hdx : HasFourierPartial 0 φ dx)
    (hdy : HasFourierPartial 1 φ dy) :
    IntegrableOn (fun p ↦ ddMatrixForm p (liftL2 dx p) (liftL2 dy p)) cellSquare ∧
      IntegrableOn (ddPiconeGradient φ dx dy) cellSquare := by
  obtain ⟨mA, mB⟩ := even_h2_diagonal_gradient_division hφ hs hdx hdy
  have hbc : Bornology.IsBounded cellSquare :=
    isBounded_cellNeighbourhood.subset fun _ hp ↦
      closure_cellSquare_subset_cellNeighbourhood (subset_closure hp)
  have mx := memLp_liftL2 dx hbc
  have my := memLp_liftL2 dy hbc
  refine ⟨ddMatrixForm_integrable_of_diagonal mx my mA mB, ?_⟩
  let A := fun p ↦ (liftL2 dx p + liftL2 dy p) / (cos (diagCoord p).1 : ℂ) -
    liftL2 φ p * (groundDiagonal 0 p : ℂ)
  let B := fun p ↦ (liftL2 dx p - liftL2 dy p) / (cos (diagCoord p).2 : ℂ) -
    liftL2 φ p * (groundDiagonal 1 p : ℂ)
  have mground (j) := memLp_mul_real_bounded (memLp_liftL2 φ hbc)
    (measurable_groundDiagonal j) (groundDiagonal_bound j)
  have ma : MemLp A 2 (volume.restrict cellSquare) := mA.sub (mground 0)
  have mb : MemLp B 2 (volume.restrict cellSquare) := mB.sub (mground 1)
  let ca := fun p ↦ cos (diagCoord p).1
  let cb := fun p ↦ cos (diagCoord p).2
  have mca : Measurable ca := by dsimp [ca, diagCoord]; fun_prop
  have mcb : Measurable cb := by dsimp [cb, diagCoord]; fun_prop
  have mCa := memLp_mul_real_bounded ma mca (fun p ↦ abs_cos_le_one _)
  have mCb := memLp_mul_real_bounded mb mcb (fun p ↦ abs_cos_le_one _)
  let Vx := fun p ↦ (1 / 2 : ℂ) * (A p * (ca p : ℂ) + B p * (cb p : ℂ))
  let Vy := fun p ↦ (1 / 2 : ℂ) * (A p * (ca p : ℂ) - B p * (cb p : ℂ))
  have mvx : MemLp Vx 2 (volume.restrict cellSquare) := (mCa.add mCb).const_mul (1 / 2)
  have mvy : MemLp Vy 2 (volume.restrict cellSquare) := (mCa.sub mCb).const_mul (1 / 2)
  have hcos (p : ℝ × ℝ) (hp : p ∈ cellSquare) :
      (ca p : ℂ) ≠ 0 ∧ (cb p : ℂ) ≠ 0 := by
    constructor <;> apply Complex.ofReal_ne_zero.mpr <;> apply ne_of_gt
    · exact cos_pos_of_mem_Ioo (abs_lt.mp hp.1)
    · exact cos_pos_of_mem_Ioo (abs_lt.mp hp.2)
  have hNa (p : ℝ × ℝ) (hp : p ∈ cellSquare) :
      (Vx p + Vy p) / (cos (diagCoord p).1 : ℂ) = A p := by
    dsimp only [Vx, Vy]
    change ((1 / 2 : ℂ) * (A p * (ca p : ℂ) + B p * (cb p : ℂ)) +
      (1 / 2 : ℂ) * (A p * (ca p : ℂ) - B p * (cb p : ℂ))) / (ca p : ℂ) = _
    field_simp [(hcos p hp).1]
    ring
  have hNb (p : ℝ × ℝ) (hp : p ∈ cellSquare) :
      (Vx p - Vy p) / (cos (diagCoord p).2 : ℂ) = B p := by
    dsimp only [Vx, Vy]
    change ((1 / 2 : ℂ) * (A p * (ca p : ℂ) + B p * (cb p : ℂ)) -
      (1 / 2 : ℂ) * (A p * (ca p : ℂ) - B p * (cb p : ℂ))) / (cb p : ℂ) = _
    field_simp [(hcos p hp).2]
    ring
  have mNa := ma.ae_eq (ae_restrict_of_forall_mem isOpen_cellSquare.measurableSet
    (fun p hp ↦ (hNa p hp).symm))
  have mNb := mb.ae_eq (ae_restrict_of_forall_mem isOpen_cellSquare.measurableSet
    (fun p hp ↦ (hNb p hp).symm))
  apply (ddMatrixForm_integrable_of_diagonal mvx mvy mNa mNb).congr
  filter_upwards [ae_regular_cell] with p hp
  have hg := groundDiagonal_eq hp.2
  have hga := congrArg (fun x : ℝ ↦ (x : ℂ)) hg.1
  have hgb := congrArg (fun x : ℝ ↦ (x : ℂ)) hg.2
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_sub] at hga hgb
  have hw : (ddGround p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (zero_lt_one.trans_le (one_le_ddGround p)))
  have hpa : A p * (ca p : ℂ) = liftL2 dx p + liftL2 dy p -
      liftL2 φ p * (((partialX ddGround p : ℝ) : ℂ) + ((partialY ddGround p : ℝ) : ℂ)) /
        (ddGround p : ℂ) := by
    have he : A p * (ca p : ℂ) = liftL2 dx p + liftL2 dy p -
        liftL2 φ p * ((ca p : ℂ) * (groundDiagonal 0 p : ℂ)) := by
      dsimp only [A]
      change ((liftL2 dx p + liftL2 dy p) / (ca p : ℂ) -
        liftL2 φ p * (groundDiagonal 0 p : ℂ)) * (ca p : ℂ) = _
      field_simp [(hcos p hp.1).1]
    rw [he, hga]
    ring
  have hpb : B p * (cb p : ℂ) = liftL2 dx p - liftL2 dy p -
      liftL2 φ p * (((partialX ddGround p : ℝ) : ℂ) - ((partialY ddGround p : ℝ) : ℂ)) /
        (ddGround p : ℂ) := by
    have he : B p * (cb p : ℂ) = liftL2 dx p - liftL2 dy p -
        liftL2 φ p * ((cb p : ℂ) * (groundDiagonal 1 p : ℂ)) := by
      dsimp only [B]
      change ((liftL2 dx p - liftL2 dy p) / (cb p : ℂ) -
        liftL2 φ p * (groundDiagonal 1 p : ℂ)) * (cb p : ℂ) = _
      field_simp [(hcos p hp.1).2]
    rw [he, hgb]
    ring
  have hvx : Vx p = (ddGround p : ℂ) * ddDividedPartial φ dx 0 p := by
    dsimp only [Vx]
    rw [hpa, hpb]
    simp only [ddDividedPartial, coordPartial, ↓reduceIte]
    field_simp [hw]
    ring
  have hvy : Vy p = (ddGround p : ℂ) * ddDividedPartial φ dy 1 p := by
    dsimp only [Vy]
    rw [hpa, hpb]
    simp only [ddDividedPartial, coordPartial, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
    field_simp [hw]
    ring
  rw [hvx, hvy, ddMatrixForm_real_mul]
  rfl

end NoEmbeddedEigenvalues
