module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.NormalAverage
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.RadialWeakMultiplier
public import EulerDipoleEigenvalues.Regularity.SaddleElliptic.ScaledInteriorEnergy
public import Mathlib.Topology.Compactness.Lindelof
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.SobolevGluing

/-! # Weighted division on the two coordinate cones -/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal

private def diskCone (ρ : ℝ) : Set (ℝ × ℝ) :=
  localDisk 0 ρ ∩ {p | |p.2| < 2 * |p.1|}

private theorem isOpen_diskCone (ρ : ℝ) : IsOpen (diskCone ρ) :=
  (isOpen_localDisk 0 ρ).inter
    (isOpen_lt continuous_snd.abs (continuous_const.mul continuous_fst.abs))

private theorem diskCone_fst_ne {ρ : ℝ} {p : ℝ × ℝ} (hp : p ∈ diskCone ρ) : p.1 ≠ 0 := by
  intro h
  have hl : |p.2| < 2 * |p.1| := hp.2
  simp [h, not_lt_of_ge (abs_nonneg _)] at hl

private theorem radius_sq (p : ℝ × ℝ) : localRadius 0 p ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  simpa only [localRadius, Prod.fst_zero, Prod.snd_zero, sub_zero] using
    Real.sq_sqrt (show 0 ≤ p.1 ^ 2 + p.2 ^ 2 by positivity)

private theorem abs_fst_le_radius (p : ℝ × ℝ) : |p.1| ≤ localRadius 0 p := by
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  change |p.1| ^ 2 ≤ localRadius 0 p ^ 2
  rw [sq_abs, radius_sq]
  linarith [sq_nonneg p.2]

private theorem radius_le_three_abs_fst {ρ : ℝ} {p : ℝ × ℝ} (hp : p ∈ diskCone ρ) :
    localRadius 0 p ≤ 3 * |p.1| := by
  have h := pow_le_pow_left₀ (abs_nonneg p.2) hp.2.le 2
  change |p.2| ^ 2 ≤ (2 * |p.1|) ^ 2 at h
  rw [mul_pow, sq_abs, sq_abs] at h
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  change localRadius 0 p ^ 2 ≤ (3 * |p.1|) ^ 2
  rw [radius_sq, mul_pow, sq_abs]
  linarith only [h, sq_nonneg p.1]

private theorem radius_swap (p : ℝ × ℝ) : localRadius 0 p.swap = localRadius 0 p := by
  simp [localRadius, add_comm]

private theorem normalScale_radius_le (p : ℝ × ℝ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    localRadius 0 (normalScale t p) ≤ localRadius 0 p := by
  have ha : |t * p.2| ≤ |p.2| := by
    rw [abs_mul, abs_of_pos ht.1]
    exact mul_le_of_le_one_left (abs_nonneg _) ht.2.le
  have h := pow_le_pow_left₀ (abs_nonneg _) ha 2
  simp only [sq_abs] at h
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp
  change localRadius 0 (normalScale t p) ^ 2 ≤ localRadius 0 p ^ 2
  simpa only [radius_sq, normalScale, add_le_add_iff_left] using h

private theorem normalScale_disk (ρ : ℝ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    MapsTo (normalScale t) (localDisk 0 ρ) (localDisk 0 ρ) := fun p hp ↦
  (normalScale_radius_le p ht).trans_lt hp

private theorem normalScale_cone (ρ : ℝ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    MapsTo (normalScale t) (diskCone ρ) (diskCone ρ) := by
  rintro p ⟨hp, hq⟩
  refine ⟨normalScale_disk ρ t ht hp, ?_⟩
  change |t * p.2| < 2 * |p.1|
  rw [abs_mul, abs_of_pos ht.1]
  exact (mul_le_of_le_one_left (abs_nonneg _) ht.2.le).trans_lt hq

private theorem disk_finite (ρ : ℝ) : IsFiniteMeasure (volume.restrict (localDisk 0 ρ)) := by
  have hs : localDisk 0 ρ ⊆ ellipticAnnulus 0 (-1) ρ := fun p hp ↦
    ⟨(by norm_num : (-1 : ℝ) < 0).trans_le (Real.sqrt_nonneg _), hp⟩
  exact isFiniteMeasure_restrict.mpr ((measure_mono (hs.trans subset_closure)).trans_lt
    ((isCompact_closure_ellipticAnnulus 0 (-1) ρ).measure_lt_top (μ := volume))).ne

private theorem cone_finite (ρ : ℝ) : IsFiniteMeasure (volume.restrict (diskCone ρ)) := by
  let := disk_finite ρ
  exact isFiniteMeasure_restrict.mpr ((measure_mono
    (inter_subset_left : diskCone ρ ⊆ localDisk 0 ρ)).trans_lt
    ((isFiniteMeasure_restrict (μ := volume)).mp (disk_finite ρ)).lt_top).ne

/-- Symmetric rectangles contained in the disk cover it, even near the poles. -/
private theorem disk_normal_rectangle {ρ : ℝ} {p : ℝ × ℝ} (hp : p ∈ localDisk 0 ρ) :
    ∃ l r b : ℝ, l < r ∧ 0 < b ∧ p ∈ Ioo l r ×ˢ Ioo (-b) b ∧
      Ioo l r ×ˢ Ioo (-b) b ⊆ localDisk 0 ρ := by
  have hr : (p.1, |p.2|) ∈ localDisk 0 ρ := by
    have he : localRadius 0 (p.1, |p.2|) = localRadius 0 p := by simp [localRadius, sq_abs]
    exact he.trans_lt hp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_localDisk 0 ρ) _ hr
  let b := |p.2| + ε / 2
  have hε' : ε / 2 < ε := by linarith
  have hy : |p.2| < b := by dsimp [b]; linarith
  refine ⟨p.1 - ε / 2, p.1 + ε / 2, b, by linarith, (abs_nonneg _).trans_lt hy,
    ⟨⟨by linarith, by linarith⟩, abs_lt.mp hy⟩, ?_⟩
  rintro ⟨x, y⟩ ⟨hx, hy'⟩
  have hxb : (x, b) ∈ Metric.ball (p.1, |p.2|) ε := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    change |x - p.1| < ε ∧ abs (b - |p.2|) < ε
    refine ⟨abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
    rw [show b - |p.2| = ε / 2 by dsimp [b]; ring, abs_of_pos (half_pos hε)]
    exact hε'
  have hyb : |y| < b := abs_lt.mpr hy'
  have hle : localRadius 0 (x, y) ≤ localRadius 0 (x, b) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp
    change localRadius 0 (x, y) ^ 2 ≤ localRadius 0 (x, b) ^ 2
    simpa only [radius_sq, add_le_add_iff_left, sq_abs] using
      pow_le_pow_left₀ (abs_nonneg y) hyb.le 2
  exact hle.trans_lt (hball hxb)

private theorem disk_eq_mul_average {ρ : ℝ} {R d : ℝ × ℝ → ℂ}
    (hw : HasWeakPartialOn (localDisk 0 ρ) 1 R d)
    (hR : MemLp R 2 (volume.restrict (localDisk 0 ρ)))
    (hd : MemLp d 2 (volume.restrict (localDisk 0 ρ))) (hdm : Measurable d)
    (ho : ∀ᵐ p ∂volume.restrict (localDisk 0 ρ), R (axisReflect 1 p) = -R p) :
    ∀ᵐ p ∂volume.restrict (localDisk 0 ρ), R p = (p.2 : ℂ) * normalAverage 0 d p := by
  classical
  let U := localDisk 0 ρ
  choose l r b hlr hb hp hsub using fun p : U ↦ disk_normal_rectangle p.property
  let W (p : U) := Ioo (l p) (r p) ×ˢ Ioo (-b p) (b p)
  obtain ⟨S, hS, hsu⟩ := TopologicalSpace.isOpen_iUnion_countable
    W (fun p ↦ isOpen_Ioo.prod isOpen_Ioo)
  have hcover : U = ⋃ p ∈ S, W p := by
    rw [hsu]
    exact subset_antisymm (fun p hp' ↦ mem_iUnion.2 ⟨⟨p, hp'⟩, hp _⟩)
      (iUnion_subset hsub)
  change ∀ᵐ p ∂volume.restrict U, _
  rw [hcover]
  apply (ae_restrict_biUnion_iff W hS _).2
  intro i _
  have hm := Measure.restrict_mono (hsub i) (le_refl (volume : Measure (ℝ × ℝ)))
  exact (hw.mono (hsub i)).eq_mul_normalAverage_of_odd (hb i) (hlr i)
    (hR.mono_measure hm) (hd.mono_measure hm) hdm (ae_mono hm ho)

private def divX (n : ℕ) (f : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  ((p.1 : ℂ) ^ n)⁻¹ * f p

private theorem average_divX (n k : ℕ) (f : ℝ × ℝ → ℂ) :
    normalAverage k (divX n f) = divX n (normalAverage k f) := by
  funext p
  unfold normalAverage divX
  rw [← integral_const_mul]
  congr 1
  funext s
  simp only [normalKernel, normalScale, Complex.real_smul]
  ring

private def tangent (j : Fin 2) : ℂ := if j = 0 then 1 else 0

private theorem weak_divX {ρ : ℝ} {f d : ℝ × ℝ → ℂ} {j : Fin 2}
    (h : HasWeakPartialOn (diskCone ρ) j f d) (n : ℕ) :
    HasWeakPartialOn (diskCone ρ) j (divX n f)
      (fun p ↦ -(n : ℂ) * tangent j * divX (n + 1) f p + divX n d p) := by
  let χ : ℝ × ℝ → ℂ := fun p ↦ ((p.1 : ℂ) ^ n)⁻¹
  have hc : ContDiffOn ℝ ∞ χ (diskCone ρ) :=
    ((Complex.ofRealCLM.contDiff.comp contDiff_fst).pow n).contDiffOn.inv
      fun p hp ↦ pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (diskCone_fst_ne hp))
  refine (h.mul_contDiffOn (isOpen_diskCone ρ) hc).congr_ae_on
    (isOpen_diskCone ρ).measurableSet (Eventually.of_forall fun _ _ ↦ rfl)
    (Eventually.of_forall fun p hp ↦ ?_)
  have hχ : coordPartial j χ p = -(n : ℂ) * tangent j * ((p.1 : ℂ) ^ (n + 1))⁻¹ := by
    fin_cases j
    · change deriv (fun x : ℝ ↦ ((x : ℂ) ^ n)⁻¹) p.1 =
        -(n : ℂ) * 1 * ((p.1 : ℂ) ^ (n + 1))⁻¹
      have hz : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (diskCone_fst_ne hp)
      have hd : HasDerivAt (fun x : ℝ ↦ (x : ℂ)) 1 p.1 := Complex.ofRealCLM.hasFDerivAt.hasDerivAt
      have hd' := ((hd.pow n).inv (pow_ne_zero n hz)).deriv
      change deriv (fun x : ℝ ↦ ((x : ℂ) ^ n)⁻¹) p.1 = _ at hd'
      rw [hd']
      cases n with
      | zero => simp
      | succ n =>
        push_cast
        simp only [Pi.pow_apply, pow_succ, mul_one]
        field_simp
    · change deriv (fun _ : ℝ ↦ ((p.1 : ℂ) ^ n)⁻¹) p.2 =
        -(n : ℂ) * 0 * ((p.1 : ℂ) ^ (n + 1))⁻¹
      simp
  rw [hχ]
  simp only [divX, χ, mul_assoc]

private def EnergyLE (U : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℂ) (B : ℝ) : Prop :=
  MemLp f 2 (volume.restrict U) ∧ squareEnergy U f ≤ B

private theorem EnergyLE.mono_bound {U : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℂ} {B C : ℝ}
    (hf : EnergyLE U f B) (h : B ≤ C) : EnergyLE U f C :=
  ⟨hf.1, hf.2.trans h⟩

private theorem EnergyLE.dominate {U : Set (ℝ × ℝ)} {f g : ℝ × ℝ → ℂ} {B c : ℝ}
    (hg : EnergyLE U g B) (hf : AEStronglyMeasurable f (volume.restrict U))
    (h : ∀ᵐ p ∂volume.restrict U, ‖f p‖ ≤ c * ‖g p‖) :
    EnergyLE U f (c ^ 2 * B) := by
  have hl := hg.1.of_le_mul hf h
  refine ⟨hl, ?_⟩
  unfold squareEnergy
  refine (integral_mono_ae (hl.integrable_norm_pow (by decide))
    ((hg.1.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).const_mul (c ^ 2)) ?_).trans ?_
  · filter_upwards [h] with p hp
    change ‖f p‖ ^ 2 ≤ c ^ 2 * ‖g p‖ ^ 2
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hp _
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hg.2 (sq_nonneg _)

private theorem EnergyLE.add {U : Set (ℝ × ℝ)} {f g : ℝ × ℝ → ℂ} {B C : ℝ}
    (hf : EnergyLE U f B) (hg : EnergyLE U g C) :
    EnergyLE U (fun p ↦ f p + g p) (2 * (B + C)) := by
  have hl := hf.1.add hg.1
  refine ⟨hl, ?_⟩
  have hiF := hf.1.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hiG := hg.1.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  unfold squareEnergy at *
  have hh : (∫ p in U, ‖f p + g p‖ ^ 2) ≤ ∫ p in U, 2 * (‖f p‖ ^ 2 + ‖g p‖ ^ 2) := by
    apply integral_mono_ae (hl.integrable_norm_pow (by decide)) ((hiF.add hiG).const_mul _)
    exact Eventually.of_forall fun p ↦
      (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (f p) (g p)) 2).trans (by
        change (‖f p‖ + ‖g p‖) ^ 2 ≤ 2 * (‖f p‖ ^ 2 + ‖g p‖ ^ 2)
        nlinarith [sq_nonneg (‖f p‖ - ‖g p‖)])
  rw [integral_const_mul, integral_add hiF hiG] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add hf.2 hg.2) (by norm_num))

private theorem EnergyLE.const_mul_bound {U : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℂ} {B c : ℝ}
    (hf : EnergyLE U f B) {a : ℂ} (ha : ‖a‖ ≤ c) :
    EnergyLE U (fun p ↦ a * f p) (c ^ 2 * B) :=
  hf.dominate (hf.1.aestronglyMeasurable.const_mul a) (Eventually.of_forall fun p ↦ by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ha (norm_nonneg _))

private theorem energy_word_le {k s : ℕ} {U : Set (ℝ × ℝ)}
    (D : List (Fin 2) → ℝ × ℝ → ℂ) (w : List (Fin 2)) (hw : w.length = k) :
    squareEnergy U (fun p ↦ D w p / (localRadius 0 p ^ s : ℂ)) ≤ radialJetEnergy k s U 0 D := by
  let v : Fin k → Fin 2 := fun i ↦ w.get (Fin.cast hw.symm i)
  have hv : List.ofFn v = w := (List.ofFn_congr hw w.get).symm.trans (List.ofFn_get w)
  rw [← hv]
  exact Finset.single_le_sum
    (f := fun v : Fin k → Fin 2 ↦
      squareEnergy U (fun p ↦ D (List.ofFn v) p / (localRadius 0 p ^ s : ℂ)))
    (fun _ _ ↦ squareEnergy_nonneg _ _) (Finset.mem_univ v)

private theorem radialEnergy_nonneg (k s : ℕ) (U : Set (ℝ × ℝ))
    (D : List (Fin 2) → ℝ × ℝ → ℂ) : 0 ≤ radialJetEnergy k s U 0 D :=
  Finset.sum_nonneg fun _ _ ↦ integral_nonneg fun _ ↦ sq_nonneg _

private theorem average_divX_bound {ρ : ℝ} {f : ℝ × ℝ → ℂ} (hfm : Measurable f)
    {B : ℝ} {k a b : ℕ} (hab : a + b ≤ 3)
    (hf : EnergyLE (localDisk 0 ρ) (fun p ↦ f p / (localRadius 0 p ^ (a + b) : ℂ)) B) :
    EnergyLE (diskCone ρ)
      (fun p ↦ divX a (normalAverage k f) p / (localRadius 0 p ^ b : ℂ)) (4 * 27 ^ 2 * B) := by
  let := cone_finite ρ
  let U := diskCone ρ
  have hm : Measurable (divX (a + b) f) := by unfold divX; fun_prop
  have hU : MeasurableSet U := (isOpen_diskCone ρ).measurableSet
  have hsub : U ⊆ localDisk 0 ρ := inter_subset_left
  have hF : EnergyLE U (fun p ↦ f p / (localRadius 0 p ^ (a + b) : ℂ)) B := by
    refine ⟨hf.1.mono_measure (Measure.restrict_mono hsub le_rfl), ?_⟩
    exact (setIntegral_mono_set (hf.1.integrable_norm_pow (by decide))
      (Eventually.of_forall fun _ ↦ sq_nonneg _) (Eventually.of_forall hsub)).trans hf.2
  have hg : EnergyLE U (divX (a + b) f) (27 ^ 2 * B) := by
    apply hF.dominate (c := 27) hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hU] with p hp
    have hx : 0 < |p.1| := abs_pos.mpr (diskCone_fst_ne hp)
    have hR : 0 ≤ localRadius 0 p := hx.le.trans (abs_fst_le_radius p)
    have hratio : localRadius 0 p ^ (a + b) ≤ 27 * |p.1| ^ (a + b) := by
      calc
        _ ≤ (3 * |p.1|) ^ (a + b) :=
          pow_le_pow_left₀ hR (radius_le_three_abs_fst hp) _
        _ ≤ _ := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right
            ((pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hab).trans_eq (by norm_num))
            (pow_nonneg hx.le _)
    have hRp : 0 < localRadius 0 p := hx.trans_le (abs_fst_le_radius p)
    simp only [divX, norm_mul, norm_div, norm_inv, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hR]
    rw [inv_mul_eq_div, ← mul_div_assoc]
    apply (div_le_div_iff₀ (pow_pos hx _) (pow_pos hRp _)).2
    simpa only [mul_assoc, mul_comm 27 ‖f p‖] using
      mul_le_mul_of_nonneg_left hratio (norm_nonneg (f p))
  have hA : EnergyLE U (divX (a + b) (normalAverage k f)) (4 * (27 ^ 2 * B)) := by
    rw [← average_divX]
    have h := normalAverage_memLp hU (normalScale_cone ρ) hm hg.1 k
    exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_left hg.2 (by norm_num))⟩
  have hmeas : Measurable (fun p ↦ divX a (normalAverage k f) p / (localRadius 0 p ^ b : ℂ)) := by
    have h := measurable_normalAverage k hfm
    unfold divX
    have hr := (continuous_localRadius (0 : ℝ × ℝ)).measurable
    fun_prop
  have h := hA.dominate (c := 1) hmeas.aestronglyMeasurable ?_
  · simpa only [one_pow, one_mul, mul_assoc] using h
  · filter_upwards [ae_restrict_mem hU] with p hp
    have hx := abs_pos.mpr (diskCone_fst_ne hp)
    have hR := hx.trans_le (abs_fst_le_radius p)
    simp only [divX, norm_div, norm_mul, norm_inv, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR, one_mul]
    rw [pow_add, inv_mul_eq_div, inv_mul_eq_div, div_div]
    apply div_le_div_of_nonneg_left (norm_nonneg _)
      (mul_pos (pow_pos hx _) (pow_pos hx _))
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.le (abs_fst_le_radius p) _)
      (pow_nonneg hx.le _)

private def divisionJet (Q : List (Fin 2) → ℝ × ℝ → ℂ) :
    List (Fin 2) → ℝ × ℝ → ℂ
  | [] => divX 1 (Q [])
  | [j] => fun p ↦ -tangent j * divX 2 (Q []) p + divX 1 (Q [j]) p
  | [i, j] => fun p ↦
      (2 * tangent j * tangent i * divX 3 (Q []) p +
        -tangent j * divX 2 (Q [i]) p) +
      (-tangent i * divX 2 (Q [j]) p + divX 1 (Q [i, j]) p)
  | _ :: _ :: _ :: _ => 0

private theorem divisionJet_weak {ρ : ℝ} {Q : List (Fin 2) → ℝ × ℝ → ℂ}
    (hQ : HasWeakJetOn 2 (diskCone ρ) (Q []) Q) :
    HasWeakJetOn 2 (diskCone ρ) (divisionJet Q []) (divisionJet Q) := by
  refine ⟨rfl, fun w hw i ↦ ?_⟩
  cases w with
  | nil =>
    simpa only [divisionJet, Nat.cast_one, neg_one_mul] using weak_divX (hQ.2 [] hw i) 1
  | cons j w =>
    cases w with
    | nil =>
      have ha := (weak_divX (hQ.2 [] (by decide) i) 2).const_mul (-tangent j)
      have hb := weak_divX (hQ.2 [j] hw i) 1
      convert ha.add hb using 1
      · rfl
      funext p
      change (2 * tangent j * tangent i * divX 3 (Q []) p +
        -tangent j * divX 2 (Q [i]) p) +
        (-tangent i * divX 2 (Q [j]) p + divX 1 (Q [i, j]) p) = _
      simp only [Nat.cast_one, Nat.cast_ofNat]
      ring
    | cons k w => simp at hw

private theorem ae_ne_axis (j : Fin 2) {U : Set (ℝ × ℝ)} :
    ∀ᵐ p ∂volume.restrict U, axisCoord j p ≠ 0 := by
  have h : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by rw [ae_iff]; simp
  apply ae_restrict_of_ae
  rw [Measure.volume_eq_prod]
  fin_cases j
  · exact Measure.quasiMeasurePreserving_fst.ae h
  · exact Measure.quasiMeasurePreserving_snd.ae h

/-- Weighted division on the cone where the tangential coordinate controls the radius. -/
private theorem division_on_cone {ρ B : ℝ} (hB : 0 ≤ B)
    {R : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hR : MemSobolevOn 3 (localDisk 0 ρ) R) (hD : HasWeakJetOn 3 (localDisk 0 ρ) R D)
    (hodd : ∀ᵐ p ∂volume.restrict (localDisk 0 ρ), R (axisReflect 1 p) = -R p)
    (hBound : ∀ w, 1 ≤ w.length → w.length ≤ 3 →
      EnergyLE (localDisk 0 ρ) (fun p ↦ D w p / (localRadius 0 p ^ (4 - w.length) : ℂ)) B) :
    ∃ E : List (Fin 2) → ℝ × ℝ → ℂ,
      HasWeakJetOn 2 (diskCone ρ) (E []) E ∧
      (∀ᵐ p ∂volume.restrict (diskCone ρ), R p = ((p.1 * p.2 : ℝ) : ℂ) * E [] p) ∧
      ∀ w, w.length ≤ 2 →
        EnergyLE (diskCone ρ) (fun p ↦ E w p / (localRadius 0 p ^ (2 - w.length) : ℂ))
          (64 * (4 * 27 ^ 2 * B)) := by
  let U := localDisk 0 ρ
  let := disk_finite ρ
  have hU := isOpen_localDisk 0 ρ
  have hL (w : List (Fin 2)) (hw : w.length ≤ 3) := hR.memLp_weakJet hU hD w hw
  let M (w : List (Fin 2)) :=
    if hw : w.length ≤ 3 then (hL w hw).aestronglyMeasurable.mk (D w) else 0
  have hmm (w : List (Fin 2)) (hw : w.length ≤ 3) : Measurable (M w) := by
    simpa only [M, dite_eq_left hw] using
      (hL w hw).aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hme (w : List (Fin 2)) (hw : w.length ≤ 3) : D w =ᵐ[volume.restrict U] M w := by
    simpa only [M, dite_eq_left hw] using (hL w hw).aestronglyMeasurable.ae_eq_mk
  have hmL (w : List (Fin 2)) (hw : w.length ≤ 3) := (hL w hw).ae_eq (hme w hw)
  have hmw (w : List (Fin 2)) (hw : w.length < 3) (j : Fin 2) :
      HasWeakPartialOn U j (M w) (M (j :: w)) :=
    (hD.2 w hw j).congr_ae_on hU.measurableSet
      ((ae_restrict_iff' hU.measurableSet).mp (hme w hw.le))
      ((ae_restrict_iff' hU.measurableSet).mp (hme (j :: w) (by simp; omega)))
  let Q (w : List (Fin 2)) := normalAverage (w.count 1) (M (w ++ [1]))
  have hQ : HasWeakJetOn 2 U (Q []) Q := by
    refine ⟨rfl, fun w hw j ↦ ?_⟩
    have hn : (w ++ [1]).length < 3 := by simp; omega
    have hn' : (j :: (w ++ [1])).length ≤ 3 := by simp; omega
    have h := (hmw _ hn j).average_normal hU (normalScale_disk ρ)
      (hmm _ hn.le) (hmm _ hn') (hmL _ hn.le) (hmL _ hn') (w.count 1)
    have hc : (j :: w).count 1 = w.count 1 + if j = 0 then 0 else 1 := by
      fin_cases j
      · change (0 :: w).count 1 = w.count 1 + 0
        rw [List.count_cons_of_ne (by decide : (0 : Fin 2) ≠ 1), add_zero]
      · exact List.count_cons_self
    simpa only [Q, hc, List.cons_append] using h
  have hd : HasWeakPartialOn U 1 R (M [1]) := by
    have h := (hD.2 [] (by decide) 1).congr_ae_on hU.measurableSet
      (Eventually.of_forall fun _ _ ↦ rfl)
      ((ae_restrict_iff' hU.measurableSet).mp (hme [1] (by decide)))
    rwa [hD.1] at h
  have heq : ∀ᵐ p ∂volume.restrict U, R p = (p.2 : ℂ) * Q [] p :=
    disk_eq_mul_average hd hR.memLp (hmL [1] (by decide)) (hmm [1] (by decide)) hodd
  refine ⟨divisionJet Q, divisionJet_weak (hQ.mono inter_subset_left), ?_, ?_⟩
  · filter_upwards [ae_mono (Measure.restrict_mono (inter_subset_left :
      diskCone ρ ⊆ U) le_rfl) heq, ae_restrict_mem (isOpen_diskCone ρ).measurableSet] with p h hp
    rw [h, divisionJet, divX, pow_one, Complex.ofReal_mul]
    field_simp [Complex.ofReal_ne_zero.mpr (diskCone_fst_ne hp)]
  · let K : ℝ := 4 * 27 ^ 2 * B
    have hK : 0 ≤ K := by positivity
    have ht (v : List (Fin 2)) (a b : ℕ) (ha : 0 < a) (hv : a + b + v.length = 3) :
        EnergyLE (diskCone ρ) (fun p ↦ divX a (Q v) p / (localRadius 0 p ^ b : ℂ)) K := by
      have hn : (v ++ [1]).length ≤ 3 := by simp; omega
      have hn₁ : 1 ≤ (v ++ [1]).length := by simp
      have hf := hBound (v ++ [1]) hn₁ hn
      have hs : 4 - (v ++ [1]).length = a + b := by simp; omega
      rw [hs] at hf
      have hEq : (fun p ↦ D (v ++ [1]) p / (localRadius 0 p ^ (a + b) : ℂ)) =ᵐ[volume.restrict U]
          fun p ↦ M (v ++ [1]) p / (localRadius 0 p ^ (a + b) : ℂ) := by
        filter_upwards [hme _ hn] with p hp
        simp only [hp]
      exact average_divX_bound (hmm _ hn) (by omega)
        ⟨hf.1.ae_eq hEq, (integral_congr_ae (hEq.fun_comp fun z : ℂ ↦ ‖z‖ ^ 2)).symm.trans_le hf.2⟩
    have htan (j : Fin 2) : ‖-tangent j‖ ≤ 1 := by fin_cases j <;> norm_num [tangent]
    have htan2 (j i : Fin 2) : ‖2 * tangent j * tangent i‖ ≤ 2 := by
      fin_cases j <;> fin_cases i <;> norm_num [tangent]
    intro w hw
    rcases w with _ | ⟨j, _ | ⟨i, _ | ⟨m, w⟩⟩⟩
    · exact (ht [] 1 2 (by decide) (by decide)).mono_bound (by linarith)
    · have ha := (ht [] 2 1 (by decide) (by decide)).const_mul_bound (htan j)
      have hh := ha.add (ht [j] 1 1 (by decide) rfl)
      have hbound : 2 * (1 ^ 2 * K + K) ≤ 64 * K := by linarith
      simpa only [divisionJet, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
        add_div, mul_div_assoc] using hh.mono_bound hbound
    · have ha := (ht [] 3 0 (by decide) (by decide)).const_mul_bound (htan2 i j)
      have hb := (ht [j] 2 0 (by decide) rfl).const_mul_bound (htan i)
      have hc := (ht [i] 2 0 (by decide) rfl).const_mul_bound (htan j)
      have hh := (ha.add hb).add (hc.add (ht [j, i] 1 0 (by decide) rfl))
      have hbound : 2 * (2 * (2 ^ 2 * K + 1 ^ 2 * K) + 2 * (1 ^ 2 * K + K)) ≤ 64 * K := by
        linarith
      simpa only [divisionJet, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
        add_div, mul_div_assoc] using hh.mono_bound hbound
    · simp at hw

private theorem swap_preserves_volume : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) := by
  simpa only [Measure.volume_eq_prod] using
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume))

private theorem swap_mem_preimage_disk (ρ : ℝ) : Prod.swap ⁻¹' localDisk 0 ρ = localDisk 0 ρ := by
  ext p
  change localRadius 0 p.swap < ρ ↔ localRadius 0 p < ρ
  rw [radius_swap]

private theorem EnergyLE.comp_swap {U : Set (ℝ × ℝ)} (hU : MeasurableSet U)
    {f : ℝ × ℝ → ℂ} {B : ℝ} (hf : EnergyLE U f B) :
    EnergyLE (Prod.swap ⁻¹' U) (f ∘ Prod.swap) B := by
  let T := Homeomorph.prodComm ℝ ℝ
  have hmap : Measure.map T (volume.restrict (Prod.swap ⁻¹' U)) = volume.restrict U := by
    change Measure.map Prod.swap (volume.restrict (Prod.swap ⁻¹' U)) = _
    rw [← Measure.restrict_map measurable_swap hU, swap_preserves_volume.map_eq]
  refine ⟨T.measurableEmbedding.memLp_map_measure_iff.1 (hmap ▸ hf.1), ?_⟩
  unfold squareEnergy
  change (∫ p in Prod.swap ⁻¹' U, ‖f (T p)‖ ^ 2) ≤ _
  rw [← T.measurableEmbedding.integral_map (g := fun p ↦ ‖f p‖ ^ 2), hmap]
  exact hf.2

private def flipAxis (j : Fin 2) : Fin 2 := if j = 0 then 1 else 0

private theorem weak_comp_swap {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ × ℝ → ℂ} {d : Fin 2 → ℝ × ℝ → ℂ}
    (hd : ∀ j, HasWeakPartialOn U j f (d j)) (i : Fin 2) :
    HasWeakPartialOn (Prod.swap ⁻¹' U) i (f ∘ Prod.swap) (d (flipAxis i) ∘ Prod.swap) := by
  let T := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  have hT : (planeAffine T 0 : ℝ × ℝ → ℝ × ℝ) = Prod.swap := by
    funext p
    simp only [planeAffine_apply, T, ContinuousLinearEquiv.prodComm_apply, add_zero]
  have hmp : MeasurePreserving (planeAffine T 0) := hT ▸ swap_preserves_volume
  have h := HasWeakPartialOn.comp_planeAffine T 0 hmp hU hd i
  rw [hT] at h
  fin_cases i
  · change HasWeakPartialOn (Prod.swap ⁻¹' U) 0 (f ∘ Prod.swap) (fun p ↦ d 1 p.swap)
    have h₀ : affineCoeff T 0 0 = 0 := rfl
    have h₁ : affineCoeff T 1 0 = 1 := rfl
    change HasWeakPartialOn (Prod.swap ⁻¹' U) 0 (f ∘ Prod.swap)
      (fun p ↦ affineCoeff T 0 0 * d 0 p.swap + affineCoeff T 1 0 * d 1 p.swap) at h
    simpa only [h₀, h₁, zero_mul, one_mul, zero_add] using h
  · change HasWeakPartialOn (Prod.swap ⁻¹' U) 1 (f ∘ Prod.swap) (fun p ↦ d 0 p.swap)
    have h₀ : affineCoeff T 0 1 = 1 := rfl
    have h₁ : affineCoeff T 1 1 = 0 := rfl
    change HasWeakPartialOn (Prod.swap ⁻¹' U) 1 (f ∘ Prod.swap)
      (fun p ↦ affineCoeff T 0 1 * d 0 p.swap + affineCoeff T 1 1 * d 1 p.swap) at h
    simpa only [h₀, h₁, zero_mul, one_mul, add_zero] using h

private theorem weakJet_comp_swap {n : ℕ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : HasWeakJetOn n U f D) :
    HasWeakJetOn n (Prod.swap ⁻¹' U) (f ∘ Prod.swap)
      (fun w ↦ D (w.map flipAxis) ∘ Prod.swap) :=
  ⟨congrArg (· ∘ Prod.swap) hD.1, fun w hw j ↦
    weak_comp_swap hU (hD.2 (w.map flipAxis) (by simpa only [List.length_map] using hw)) j⟩

private theorem ae_comp_swap {U : Set (ℝ × ℝ)} {P : (ℝ × ℝ) → Prop}
    (h : ∀ᵐ p ∂volume.restrict U, P p) :
    ∀ᵐ p ∂volume.restrict (Prod.swap ⁻¹' U), P p.swap :=
  (swap_preserves_volume.quasiMeasurePreserving.restrict
    (show MapsTo Prod.swap (Prod.swap ⁻¹' U) U from fun _ hp ↦ hp)).ae h

private theorem cone_union (ρ : ℝ) :
    diskCone ρ ∪ Prod.swap ⁻¹' diskCone ρ = localDisk 0 ρ \ {0} := by
  ext p
  change (p ∈ diskCone ρ ∨ p.swap ∈ diskCone ρ) ↔
    (p ∈ localDisk 0 ρ ∧ p ≠ 0)
  have hs (q : ℝ × ℝ) (hq : q ∈ diskCone ρ) : q ≠ 0 := by
    intro he
    exact diskCone_fst_ne hq (by rw [he]; rfl)
  constructor
  · rintro (h | h)
    · exact ⟨h.1, hs _ h⟩
    · refine ⟨?_, fun he ↦ hs _ h ?_⟩
      · have hh : localRadius 0 p.swap < ρ := h.1
        rwa [radius_swap] at hh
      · rw [he]; rfl
  · rintro ⟨hp, hn⟩
    by_cases h : |p.2| < 2 * |p.1|
    · exact Or.inl ⟨hp, h⟩
    · right
      refine ⟨?_, ?_⟩
      · change localRadius 0 p.swap < ρ
        rwa [radius_swap]
      · change |p.1| < 2 * |p.2|
        have he : 0 < |p.2| := by
          by_contra! hz
          have h₀ : |p.2| = 0 := le_antisymm hz (abs_nonneg _)
          have h₁ : |p.1| = 0 := by
            linarith only [h₀, le_of_not_gt h, abs_nonneg p.1]
          exact hn (Prod.ext (abs_eq_zero.mp h₁) (abs_eq_zero.mp h₀))
        linarith only [he, le_of_not_gt h]

private theorem EnergyLE.union {U V : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℂ} {B C : ℝ}
    (hU : EnergyLE U f B) (hV : EnergyLE V f C) :
    EnergyLE (U ∪ V) f (B + C) := by
  have hm := Measure.restrict_union_le (μ := (volume : Measure (ℝ × ℝ))) U V
  have hi := (hU.1.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).add_measure
    (hV.1.integrable_norm_pow (by decide))
  have hFm := hU.1.aestronglyMeasurable.add_measure hV.1.aestronglyMeasurable
  refine ⟨((memLp_two_iff_integrable_sq_norm hFm).mpr hi).mono_measure hm, ?_⟩
  unfold squareEnergy
  have h := integral_mono_measure hm (Eventually.of_forall fun p ↦ sq_nonneg ‖f p‖) hi
  rw [integral_add_measure (hU.1.integrable_norm_pow (by decide))
      (hV.1.integrable_norm_pow (by decide))] at h
  exact h.trans (add_le_add hU.2 hV.2)

private theorem EnergyLE.ae_eq {U : Set (ℝ × ℝ)} {f g : ℝ × ℝ → ℂ} {B : ℝ}
    (hf : EnergyLE U f B) (h : f =ᵐ[volume.restrict U] g) : EnergyLE U g B :=
  ⟨hf.1.ae_eq h, (integral_congr_ae (h.fun_comp fun z : ℂ ↦ ‖z‖ ^ 2)).symm.trans_le hf.2⟩

private theorem EnergyLE.congr_domain {U V : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℂ} {B : ℝ}
    (h : volume.restrict U = volume.restrict V) (hf : EnergyLE U f B) : EnergyLE V f B := by
  unfold EnergyLE squareEnergy at *
  rwa [← h]

private theorem patch_weakJet {U A B : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hA : IsOpen A) (hB : IsOpen B) (hcov : U = A ∪ B)
    {E : List (Fin 2) → ℝ × ℝ → ℂ}
    (ha : HasWeakJetOn 2 A (E []) E) (hb : HasWeakJetOn 2 B (E []) E)
    (hL : ∀ w, w.length ≤ 2 → MemLp (E w) 2 (volume.restrict U)) :
    HasWeakJetOn 2 U (E []) E := by
  have haU : A ⊆ U := hcov ▸ subset_union_left
  have hbU : B ⊆ U := hcov ▸ subset_union_right
  have ha₂ := memSobolevOn_iff_exists_weakJet.mpr
    ⟨E, ha, fun w hw ↦ (hL w hw).mono_measure (Measure.restrict_mono haU le_rfl)⟩
  have hb₂ := memSobolevOn_iff_exists_weakJet.mpr
    ⟨E, hb, fun w hw ↦ (hL w hw).mono_measure (Measure.restrict_mono hbU le_rfl)⟩
  have hloc : MemSobolevLocOn 2 U (E []) := by
    apply memSobolevLocOn_of_locally
    intro p hp
    rw [hcov] at hp
    exact hp.elim (fun h ↦ ⟨A, hA, h, ha₂.memSobolevLocOn⟩)
      fun h ↦ ⟨B, hB, h, hb₂.memSobolevLocOn⟩
  refine ⟨rfl, fun w hw j ↦ ?_⟩
  have hlen : (j :: w).length ≤ 2 := by simp; omega
  have hi {v : List (Fin 2)} (hv : v.length ≤ 2) : LocallyIntegrableOn (E v) U :=
    locallyIntegrableOn_of_locallyIntegrable_restrict ((hL v hv).locallyIntegrable (by norm_num))
  refine ⟨hi hw.le, hi hlen, fun φ hφ ↦ ?_⟩
  obtain ⟨W, hW, hφW, hWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure hφ.hasCompactSupport hU hφ.tsupport_subset
  obtain ⟨F, hF, _⟩ := memSobolevOn_iff_exists_weakJet.mp (hloc W hW hWc hWU)
  have hEq (v : List (Fin 2)) (hv : v.length ≤ 2) : F v =ᵐ[volume.restrict W] E v := by
    have hWAB : W = (W ∩ A) ∪ (W ∩ B) := by
      rw [← inter_union_distrib_left, ← hcov]
      exact (inter_eq_left.mpr (subset_closure.trans hWU)).symm
    change ∀ᵐ p ∂volume.restrict W, F v p = E v p
    rw [hWAB, ae_restrict_union_iff]
    exact ⟨(ae_restrict_iff' (hW.inter hA).measurableSet).mpr
      ((hF.mono inter_subset_left).ae_eq (hW.inter hA) (ha.mono inter_subset_right) v hv),
      (ae_restrict_iff' (hW.inter hB).measurableSet).mpr
      ((hF.mono inter_subset_left).ae_eq (hW.inter hB) (hb.mono inter_subset_right) v hv)⟩
  have h := (hF.2 w hw j).congr_ae_on hW.measurableSet
    ((ae_restrict_iff' hW.measurableSet).mp (hEq w hw.le))
    ((ae_restrict_iff' hW.measurableSet).mp (hEq (j :: w) hlen))
  exact h.2.2 φ ⟨hφ.contDiff, hφ.hasCompactSupport, hφW⟩

/-- Weighted double division (`lem:weighted-double-division`), in squared-energy form.
No fourth derivative and no weighted order-zero hypothesis on R is imposed. -/
theorem weighted_double_division {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ),
      MemSobolevOn 3 (localDisk 0 ρ) R → HasWeakJetOn 3 (localDisk 0 ρ) R D →
      (∀ j, ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), R (axisReflect j p) = -R p) →
      RadialJetLp 1 3 (localDisk 0 ρ) 0 D →
      RadialJetLp 2 2 (localDisk 0 ρ) 0 D →
      RadialJetLp 3 1 (localDisk 0 ρ) 0 D →
      ∃ (V : ℝ × ℝ → ℂ) (E : List (Fin 2) → ℝ × ℝ → ℂ),
        MemSobolevLocOn 2 (localDisk 0 ρ \ {0}) V ∧
        HasWeakJetOn 2 (localDisk 0 ρ \ {0}) V E ∧
        (∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), R p = ((p.1 * p.2 : ℝ) : ℂ) * V p) ∧
        RadialJetLp 0 2 (localDisk 0 ρ) 0 E ∧
        RadialJetLp 1 1 (localDisk 0 ρ) 0 E ∧
        RadialJetLp 2 0 (localDisk 0 ρ) 0 E ∧
        radialJetEnergy 0 2 (localDisk 0 ρ) 0 E +
          radialJetEnergy 1 1 (localDisk 0 ρ) 0 E +
          radialJetEnergy 2 0 (localDisk 0 ρ) 0 E ≤
          C * (radialJetEnergy 1 3 (localDisk 0 ρ) 0 D +
            radialJetEnergy 2 2 (localDisk 0 ρ) 0 D +
            radialJetEnergy 3 1 (localDisk 0 ρ) 0 D) := by
  classical
  let U := localDisk 0 ρ
  let P := U \ {0}
  let A := diskCone ρ
  let B := Prod.swap ⁻¹' A
  have hU := isOpen_localDisk 0 ρ
  have hA := isOpen_diskCone ρ
  have hB : IsOpen B := hA.preimage continuous_swap
  have hP : IsOpen P := hU.sdiff isClosed_singleton
  have hcov : A ∪ B = P := cone_union ρ
  have hnull : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ≠ 0 := by
    rw [ae_iff]
    simp [Measure.volume_eq_prod]
  have hcenter : (0 : ℝ × ℝ) ∈ U := by
    simpa [U, localDisk, localRadius] using hρ
  have hsplit : P ∪ {(0 : ℝ × ℝ)} = U := sdiff_union_of_subset (singleton_subset_iff.mpr hcenter)
  have hUP : volume.restrict P = volume.restrict U := by
    apply Measure.restrict_congr_set
    rw [← hsplit]
    filter_upwards [hnull] with p hp
    simp [hp]
  refine ⟨7 * (2 * (64 * (4 * 27 ^ 2))), by norm_num, fun R D hR hD hodd h₁ h₂ h₃ ↦ ?_⟩
  let S := radialJetEnergy 1 3 U 0 D + radialJetEnergy 2 2 U 0 D + radialJetEnergy 3 1 U 0 D
  have hs₁ := radialEnergy_nonneg 1 3 U D
  have hs₂ := radialEnergy_nonneg 2 2 U D
  have hs₃ := radialEnergy_nonneg 3 1 U D
  have hS : 0 ≤ S := add_nonneg (add_nonneg hs₁ hs₂) hs₃
  have hBound (w : List (Fin 2)) (hlo : 1 ≤ w.length) (hhi : w.length ≤ 3) :
      EnergyLE U (fun p ↦ D w p / (localRadius 0 p ^ (4 - w.length) : ℂ)) S := by
    interval_cases hw : w.length
    · simpa only [hw] using
        (show EnergyLE U (fun p ↦ D w p / (localRadius 0 p ^ 3 : ℂ)) S from
          ⟨h₁ w hw, (energy_word_le D w hw).trans (by dsimp [S]; linarith only [hs₂, hs₃])⟩)
    · simpa only [hw] using
        (show EnergyLE U (fun p ↦ D w p / (localRadius 0 p ^ 2 : ℂ)) S from
          ⟨h₂ w hw, (energy_word_le D w hw).trans (by dsimp [S]; linarith only [hs₁, hs₃])⟩)
    · simpa only [hw] using
        (show EnergyLE U (fun p ↦ D w p / (localRadius 0 p ^ 1 : ℂ)) S from
          ⟨h₃ w hw, (energy_word_le D w hw).trans (by dsimp [S]; linarith only [hs₁, hs₂])⟩)
  obtain ⟨X, hX, hx, hXE⟩ := division_on_cone hS hR hD (hodd 1) hBound
  let R' := R ∘ Prod.swap
  let D' (w : List (Fin 2)) := D (w.map flipAxis) ∘ Prod.swap
  have hD' : HasWeakJetOn 3 U R' D' := by
    have h := weakJet_comp_swap hU hD
    rw [swap_mem_preimage_disk] at h
    exact h
  have hR' : MemSobolevOn 3 U R' := by
    refine memSobolevOn_iff_exists_weakJet.mpr ⟨D', hD', fun w hw ↦ ?_⟩
    have hL := hR.memLp_weakJet hU hD (w.map flipAxis) (by simpa only [List.length_map] using hw)
    have h : EnergyLE U (D (w.map flipAxis)) (squareEnergy U (D (w.map flipAxis))) :=
      ⟨hL, le_rfl⟩
    have h' := (h.comp_swap hU.measurableSet).1
    rw [swap_mem_preimage_disk] at h'
    exact h'
  have hodd' : ∀ᵐ p ∂volume.restrict U, R' (axisReflect 1 p) = -R' p := by
    have h := ae_comp_swap (hodd 0)
    rw [swap_mem_preimage_disk] at h
    exact h
  have hBound' (w : List (Fin 2)) (hlo : 1 ≤ w.length) (hhi : w.length ≤ 3) :
      EnergyLE U (fun p ↦ D' w p / (localRadius 0 p ^ (4 - w.length) : ℂ)) S := by
    have h := (hBound (w.map flipAxis) (by simpa only [List.length_map] using hlo)
      (by simpa only [List.length_map] using hhi)).comp_swap hU.measurableSet
    rw [swap_mem_preimage_disk] at h
    simpa only [Function.comp_def, D', List.length_map, radius_swap] using h
  obtain ⟨Y₀, hY₀, hy₀, hYE₀⟩ := division_on_cone hS hR' hD' hodd' hBound'
  let Y (w : List (Fin 2)) := Y₀ (w.map flipAxis) ∘ Prod.swap
  have hY : HasWeakJetOn 2 B (Y []) Y := weakJet_comp_swap hA hY₀
  have hy : ∀ᵐ p ∂volume.restrict B, R p = ((p.1 * p.2 : ℝ) : ℂ) * Y [] p := by
    filter_upwards [ae_comp_swap hy₀] with p hp
    simpa only [R', Y, Function.comp_apply, Prod.swap_swap, List.map_nil,
      Prod.fst_swap, Prod.snd_swap, mul_comm p.2 p.1] using hp
  let K := 64 * (4 * 27 ^ 2 * S)
  have hYE (w : List (Fin 2)) (hw : w.length ≤ 2) :
      EnergyLE B (fun p ↦ Y w p / (localRadius 0 p ^ (2 - w.length) : ℂ)) K := by
    have h := (hYE₀ (w.map flipAxis) (by simpa only [List.length_map] using hw)).comp_swap
      hA.measurableSet
    simpa only [Function.comp_def, Y, List.length_map, radius_swap] using h
  let E (w : List (Fin 2)) (p : ℝ × ℝ) := if p ∈ A then X w p else Y w p
  let V := E []
  have hEA (w : List (Fin 2)) : X w =ᵐ[volume.restrict A] E w := by
    filter_upwards [ae_restrict_mem hA.measurableSet] with p hp
    simp only [E, ite_eq_left hp]
  have hre (w : List (Fin 2)) (hw : w.length ≤ 2) :
      X w =ᵐ[volume.restrict (A ∩ B)] Y w := by
    have hsubA := Measure.restrict_mono (inter_subset_left : A ∩ B ⊆ A)
      (le_refl (volume : Measure (ℝ × ℝ)))
    have hsubB := Measure.restrict_mono (inter_subset_right : A ∩ B ⊆ B)
      (le_refl (volume : Measure (ℝ × ℝ)))
    have h0 : X [] =ᵐ[volume.restrict (A ∩ B)] Y [] := by
      filter_upwards [ae_mono hsubA hx, ae_mono hsubB hy,
        ae_ne_axis 0 (U := A ∩ B), ae_ne_axis 1 (U := A ∩ B)] with p h1 h2 hp₁ hp₂
      have hn : ((p.1 * p.2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_ne_zero hp₁ hp₂)
      exact mul_left_cancel₀ hn (h1.symm.trans h2)
    exact (ae_restrict_iff' (hA.inter hB).measurableSet).mpr
      ((hX.mono inter_subset_left).ae_eq_of_value_ae (hA.inter hB)
        (hY.mono inter_subset_right) h0 w hw)
  have hEB (w : List (Fin 2)) (hw : w.length ≤ 2) : Y w =ᵐ[volume.restrict B] E w := by
    have h := (ae_restrict_iff' (hA.inter hB).measurableSet).mp (hre w hw)
    filter_upwards [ae_restrict_of_ae h, ae_restrict_mem hB.measurableSet] with p hp hpB
    by_cases hpA : p ∈ A
    · simpa only [E, ite_eq_left hpA] using (hp ⟨hpA, hpB⟩).symm
    · simp only [E, ite_eq_right hpA]
  have hei (w : List (Fin 2)) (hw : w.length ≤ 2) :
      EnergyLE U (fun p ↦ E w p / (localRadius 0 p ^ (2 - w.length) : ℂ)) (K + K) := by
    have ha := (hXE w hw).ae_eq ((hEA w).mono fun p hp ↦
      congrArg (· / (localRadius 0 p ^ (2 - w.length) : ℂ)) hp)
    have hb := (hYE w hw).ae_eq ((hEB w hw).mono fun p hp ↦
      congrArg (· / (localRadius 0 p ^ (2 - w.length) : ℂ)) hp)
    exact EnergyLE.congr_domain (hcov ▸ hUP) (ha.union hb)
  have hLp (w : List (Fin 2)) (hw : w.length ≤ 2) : MemLp (E w) 2 (volume.restrict U) :=
    memLp_of_div_localRadius_pow (hei w hw).1
  have hPatch {W : Set (ℝ × ℝ)} (hW : IsOpen W)
      {Z : List (Fin 2) → ℝ × ℝ → ℂ} (hZ : HasWeakJetOn 2 W (Z []) Z)
      (he : ∀ w, w.length ≤ 2 → Z w =ᵐ[volume.restrict W] E w) :
      HasWeakJetOn 2 W V E := by
    refine ⟨rfl, fun w hw j ↦ (hZ.2 w hw j).congr_ae_on hW.measurableSet
      ((ae_restrict_iff' hW.measurableSet).mp (he w hw.le))
      ((ae_restrict_iff' hW.measurableSet).mp (he (j :: w) (by simp; omega)))⟩
  have hE : HasWeakJetOn 2 P V E :=
    patch_weakJet hP hA hB hcov.symm (hPatch hA hX fun w _ ↦ hEA w) (hPatch hB hY hEB)
      (fun w hw ↦ (hLp w hw).mono_measure (Measure.restrict_mono sdiff_subset le_rfl))
  have hV : MemSobolevOn 2 P V :=
    memSobolevOn_iff_exists_weakJet.mpr ⟨E, hE, fun w hw ↦
      (hLp w hw).mono_measure (Measure.restrict_mono sdiff_subset le_rfl)⟩
  have hProd : ∀ᵐ p ∂volume.restrict U, R p = ((p.1 * p.2 : ℝ) : ℂ) * V p := by
    rw [← hUP, ← hcov, ae_restrict_union_iff]
    constructor
    · filter_upwards [hx, hEA []] with p hp he
      exact hp.trans (congrArg (((p.1 * p.2 : ℝ) : ℂ) * ·) he)
    · filter_upwards [hy, hEB [] (by decide)] with p hp he
      exact hp.trans (congrArg (((p.1 * p.2 : ℝ) : ℂ) * ·) he)
  have hRad (k : ℕ) (hk : k ≤ 2) : RadialJetLp k (2 - k) U 0 E := by
    intro w hw
    rw [← hw]
    exact (hei w (hw ▸ hk)).1
  have hEn (k : ℕ) (hk : k ≤ 2) : radialJetEnergy k (2 - k) U 0 E ≤
      (2 : ℝ) ^ k * (K + K) := by
    unfold radialJetEnergy
    calc
      _ ≤ ∑ _w : Fin k → Fin 2, (K + K) := by
        apply Finset.sum_le_sum
        intro w _
        have h := (hei (List.ofFn w) (List.length_ofFn.trans_le hk)).2
        simpa only [List.length_ofFn, squareEnergy] using h
      _ = _ := by simp [mul_add]
  refine ⟨V, E, hV.memSobolevLocOn, hE, hProd, hRad 0 (by decide),
    hRad 1 (by decide), hRad 2 (by decide), ?_⟩
  have h := add_le_add (add_le_add (hEn 0 (by decide)) (hEn 1 (by decide))) (hEn 2 (by decide))
  change radialJetEnergy 0 2 U 0 E + radialJetEnergy 1 1 U 0 E + radialJetEnergy 2 0 U 0 E ≤ _
  exact h.trans_eq (by dsimp only [K]; ring)

end EulerDipoleEigenvalues
