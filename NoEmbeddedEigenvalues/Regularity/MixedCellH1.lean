import NoEmbeddedEigenvalues.Regularity.MixedSaddle
import NoEmbeddedEigenvalues.Regularity.SaddleLinearization
import NoEmbeddedEigenvalues.StreamJet

/-! # Mixed cellwise vorticity regularity

The weighted transport estimate is applied after removing a smooth
transport pair, not after dividing by a defining function of the odd sides.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped ContDiff Topology

local notation "Plane" => ℝ × ℝ

/-- The correction profile is the sum of the vorticity and forcing of its
generated transport pair. Its forcing is the profile minus the vorticity. -/
private def smoothForcing (lam : ℝ) (P : Plane → ℂ) : Plane → ℂ :=
  fun p ↦ P p - (-Complex.I / (lam : ℂ)) * classicalL0 P p

/-- Cartesian linear jet in the odd diagonal direction. -/
private def oddSaddleLinear (P : Plane) (a : ℂ) (p : Plane) : ℂ :=
  a * (((p.1 - P.1 + (p.2 - P.2)) / Real.sqrt 2 : ℝ) : ℂ)

private theorem contDiff_oddSaddleLinear (P : Plane) (a : ℂ) :
    ContDiff ℝ ∞ (oddSaddleLinear P a) := by
  unfold oddSaddleLinear
  have hc := Complex.ofRealCLM.contDiff (n := ∞)
  exact contDiff_const.mul (hc.comp (show ContDiff ℝ ∞ _ from
    ((contDiff_fst.sub contDiff_const).add (contDiff_snd.sub contDiff_const)).div_const _))

private theorem oddSaddleLinear_comp (P : Plane) (a : ℂ) :
    oddSaddleLinear P a ∘ saddleOrthoChart P = mixedAxisLinear 0 a := by
  funext q
  have hr : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simp only [Function.comp_apply, oddSaddleLinear, saddleOrthoChart, mixedAxisLinear,
    axisCoord, ite_true]
  congr 2
  field_simp
  linear_combination q.1 * (-hs)

/-- Explicit normalization of the linear correction profile. The denominator
is nonzero because the shifted saddle eigenvalue has nonzero imaginary part. -/
private def oddCorrectionCoeff (lam : ℝ) (P : Plane) (a : ℂ) : ℂ :=
  a / (1 - Complex.I / (lam : ℂ) * (Real.cos P.1 : ℂ))

private theorem oddCorrectionCoeff_mul {lam : ℝ} (hlam : lam ≠ 0) (P : Plane) (a : ℂ) :
    oddCorrectionCoeff lam P a * (1 - Complex.I / (lam : ℂ) * (Real.cos P.1 : ℂ)) = a := by
  apply div_mul_cancel₀
  rw [div_mul_eq_mul_div, show (1 : ℂ) = (lam : ℂ) / lam from
    (div_self (Complex.ofReal_ne_zero.mpr hlam)).symm, ← sub_div]
  apply div_ne_zero _ (Complex.ofReal_ne_zero.mpr hlam)
  intro he
  apply hlam
  simpa only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Complex.zero_re] using congrArg Complex.re he

private theorem partial_oddSaddleLinear (P : Plane) (a : ℂ) (j : Fin 2) (p : Plane) :
    coordPartial j (oddSaddleLinear P a) p = a * (↑(Real.sqrt 2) : ℂ)⁻¹ := by
  fin_cases j
  · exact (((((hasDerivAt_id p.1).sub_const P.1).add_const (p.2 - P.2)).div_const
      (Real.sqrt 2)).ofReal_comp.const_mul a).deriv.trans (by simp)
  · exact (((((hasDerivAt_id p.2).sub_const P.2).const_add (p.1 - P.1)).div_const
      (Real.sqrt 2)).ofReal_comp.const_mul a).deriv.trans (by simp)

private theorem smoothForcing_oddSaddleLinear (lam : ℝ) (P : Plane) (b : ℂ) :
    smoothForcing lam (oddSaddleLinear P b) =
      fun p ↦ b * (↑(Real.sqrt 2) : ℂ)⁻¹ *
        (((p.1 - P.1 + (p.2 - P.2) : ℝ) : ℂ) +
          Complex.I / (lam : ℂ) * ((Real.sin p.2 : ℂ) - (Real.sin p.1 : ℂ))) := by
  funext p
  have h₀ := partial_oddSaddleLinear P b 0 p
  have h₁ := partial_oddSaddleLinear P b 1 p
  change partialX _ _ = _ at h₀
  change partialY _ _ = _ at h₁
  simp [smoothForcing, classicalL0, h₀, h₁, Complex.real_smul, oddSaddleLinear]
  ring

private theorem first_smoothForcing_oddSaddleLinear (lam : ℝ) (P : Plane) (b : ℂ) (p : Plane) :
    coordPartial 0 (smoothForcing lam (oddSaddleLinear P b)) p =
      b * (↑(Real.sqrt 2) : ℂ)⁻¹ * (1 - Complex.I / (lam : ℂ) * (Real.cos p.1 : ℂ)) ∧
    coordPartial 1 (smoothForcing lam (oddSaddleLinear P b)) p =
      b * (↑(Real.sqrt 2) : ℂ)⁻¹ * (1 + Complex.I / (lam : ℂ) * (Real.cos p.2 : ℂ)) := by
  rw [smoothForcing_oddSaddleLinear]
  constructor
  · have hx := ((hasDerivAt_id p.1).sub_const P.1).add_const (p.2 - P.2)
    have hs := (((Real.hasDerivAt_sin p.1).ofReal_comp.const_sub
      (Real.sin p.2 : ℂ))).const_mul (Complex.I / (lam : ℂ))
    exact ((hx.ofReal_comp.add hs).const_mul _).deriv.trans (by simp [sub_eq_add_neg])
  · have hy := ((hasDerivAt_id p.2).sub_const P.2).const_add (p.1 - P.1)
    have hs := (((Real.hasDerivAt_sin p.2).ofReal_comp.sub_const
      (Real.sin p.1 : ℂ))).const_mul (Complex.I / (lam : ℂ))
    exact ((hy.ofReal_comp.add hs).const_mul _).deriv.trans (by simp)

private theorem smoothForcing_contDiff {lam : ℝ} {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (smoothForcing lam F) := by
  have hx : ContDiff ℝ ∞ (partialX F) := contDiff_coordPartial_top 0 hF
  have hy : ContDiff ℝ ∞ (partialY F) := contDiff_coordPartial_top 1 hF
  unfold smoothForcing classicalL0
  fun_prop

private theorem smoothForcing_odd_flat {P : Plane} (hP : P ∈ saddleSet)
    {lam : ℝ} (hlam : lam ≠ 0) (a : ℂ) :
    ∀ w : List (Fin 2), w.length < 3 →
      classicalComplexJet w (fun p ↦ smoothForcing lam
        (oddSaddleLinear P (oddCorrectionCoeff lam P a)) p - oddSaddleLinear P a p) P = 0 := by
  let b := oddCorrectionCoeff lam P a
  let f := smoothForcing lam (oddSaddleLinear P b)
  let L := oddSaddleLinear P a
  have hsin : Real.sin P.1 = 0 ∧ Real.sin P.2 = 0 := by
    obtain ⟨m, n, _, rfl⟩ := hP
    simp [Real.sin_int_mul_pi]
  have hf : ContDiff ℝ ∞ f := smoothForcing_contDiff (contDiff_oddSaddleLinear P b)
  have hL : ContDiff ℝ ∞ L := contDiff_oddSaddleLinear P a
  have hF0 : coordPartial 0 f = fun p ↦
      b * (↑(Real.sqrt 2) : ℂ)⁻¹ * (1 - Complex.I / (lam : ℂ) * (Real.cos p.1 : ℂ)) :=
    funext fun p ↦ (first_smoothForcing_oddSaddleLinear lam P b p).1
  have hF1 : coordPartial 1 f = fun p ↦
      b * (↑(Real.sqrt 2) : ℂ)⁻¹ * (1 + Complex.I / (lam : ℂ) * (Real.cos p.2 : ℂ)) :=
    funext fun p ↦ (first_smoothForcing_oddSaddleLinear lam P b p).2
  have hb := oddCorrectionCoeff_mul hlam P a
  change b * _ = _ at hb
  intro w hw
  change classicalComplexJet w (fun p ↦ f p - L p) P = 0
  rw [classicalComplexJet_sub_on isOpen_univ hf.contDiffOn hL.contDiffOn w (mem_univ P)]
  rcases w with _ | ⟨j, _ | ⟨k, _ | ⟨l, w⟩⟩⟩
  · simp only [classicalComplexJet, f, L, smoothForcing_oddSaddleLinear, oddSaddleLinear,
      sub_self, add_zero, zero_div, Complex.ofReal_zero, hsin.1, hsin.2, mul_zero]
  · change coordPartial j f P - coordPartial j L P = 0
    rw [partial_oddSaddleLinear]
    fin_cases j
    · change coordPartial 0 f P - _ = 0
      rw [hF0]
      dsimp only
      rw [mul_right_comm, hb, sub_self]
    · change coordPartial 1 f P - _ = 0
      rw [hF1]
      dsimp only
      rw [cos_saddle_snd hP, Complex.ofReal_neg, mul_neg, ← sub_eq_add_neg,
        mul_right_comm, hb, sub_self]
  · change coordPartial j (coordPartial k f) P - coordPartial j (coordPartial k L) P = 0
    have he : coordPartial k L = fun _ ↦ a * (↑(Real.sqrt 2) : ℂ)⁻¹ :=
      funext (partial_oddSaddleLinear P a k)
    rw [he]
    fin_cases j <;> fin_cases k
    · change coordPartial 0 (coordPartial 0 f) P - coordPartial 0 _ P = 0
      rw [hF0]
      have h := (((Real.hasDerivAt_cos P.1).ofReal_comp.const_mul
        (Complex.I / (lam : ℂ))).const_sub 1).const_mul (b * (↑(Real.sqrt 2) : ℂ)⁻¹)
      unfold coordPartial partialX
      simp only [ite_true]
      rw [h.deriv]
      simp [hsin.1]
    · change coordPartial 0 (coordPartial 1 f) P - coordPartial 0 _ P = 0
      rw [hF1]
      simp [coordPartial, partialX]
    · change coordPartial 1 (coordPartial 0 f) P - coordPartial 1 _ P = 0
      rw [hF0]
      simp [coordPartial, partialY]
    · change coordPartial 1 (coordPartial 1 f) P - coordPartial 1 _ P = 0
      rw [hF1]
      have h := (((Real.hasDerivAt_cos P.2).ofReal_comp.const_mul
        (Complex.I / (lam : ℂ))).const_add 1).const_mul (b * (↑(Real.sqrt 2) : ℂ)⁻¹)
      unfold coordPartial partialY
      try simp only [Fin.reduceEq, ite_false]
      rw [h.deriv]
      simp [hsin.2]
  · simp only [List.length_cons] at hw
    omega

private def cellSaddles : Finset Plane :=
  {(Real.pi, 0), (-Real.pi, 0), (0, Real.pi), (0, -Real.pi)}

private theorem saddle_mem_cellSaddles {P : Plane}
    (hP : P ∈ saddleSet) (hU : P ∈ cellNeighbourhood) : P ∈ cellSaddles := by
  obtain ⟨m, n, ho, rfl⟩ := hP
  have hb (k : ℝ) (hk : |k * Real.pi / 2| < 3 * Real.pi / 2) : |k| < 3 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos] at hk
    norm_num at hk
    exact lt_of_mul_lt_mul_right (by linarith : |k| * Real.pi < 3 * Real.pi) Real.pi_pos.le
  have hsR : |(m : ℝ) + n| < 3 := hb _ (by
    convert hU.1 using 1
    congr 1
    dsimp [diagCoord]
    ring)
  have hdR : |(m : ℝ) - n| < 3 := hb _ (by
    convert hU.2 using 1
    congr 1
    dsimp [diagCoord]
    ring)
  have hs : (-3 : ℤ) < m + n ∧ m + n < 3 := by exact_mod_cast abs_lt.mp hsR
  have hd : (-3 : ℤ) < m - n ∧ m - n < 3 := by exact_mod_cast abs_lt.mp hdR
  obtain ⟨j, hj⟩ := ho
  have hm : (m = 1 ∧ n = 0) ∨ (m = -1 ∧ n = 0) ∨
      (m = 0 ∧ n = 1) ∨ (m = 0 ∧ n = -1) := by omega
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [cellSaddles]

private theorem mem_saddleSet_of_mem_cellSaddles {P : Plane} (hP : P ∈ cellSaddles) :
    P ∈ saddleSet := by
  simp only [cellSaddles, Finset.mem_insert, Finset.mem_singleton] at hP
  rcases hP with rfl | rfl | rfl | rfl
  · exact ⟨1, 0, by decide, by simp⟩
  · exact ⟨-1, 0, by decide, by simp⟩
  · exact ⟨0, 1, by decide, by simp⟩
  · exact ⟨0, -1, by decide, by simp⟩

private theorem exists_smooth_odd_profile (b : Plane → ℂ) :
    ∃ F : Plane → ℂ, ContDiff ℝ ∞ F ∧
      ∀ P ∈ cellSaddles, F =ᶠ[𝓝 P] oddSaddleLinear P (b P) := by
  classical
  let ρ := Real.pi / 4
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let B (P : Plane) : ContDiffBump P := ⟨ρ, 2 * ρ, hρ, by linarith⟩
  let G (P p : Plane) := (B P p : ℂ) * oddSaddleLinear P (b P) p
  refine ⟨fun p ↦ ∑ Q ∈ cellSaddles, G Q p, ?_, ?_⟩
  · apply ContDiff.sum
    intro Q _
    exact (Complex.ofRealCLM.contDiff.comp (B Q).contDiff).mul
      (contDiff_oddSaddleLinear Q (b Q))
  · intro P hP
    filter_upwards [Metric.ball_mem_nhds P hρ] with p hp
    have hball : dist p P < ρ := hp
    have hsum : (∑ Q ∈ cellSaddles, G Q p) = G P p := by
      apply Finset.sum_eq_single_of_mem P hP
      intro Q hQ hne
      have hdist := pi_le_dist_saddles (mem_saddleSet_of_mem_cellSaddles hP)
        (mem_saddleSet_of_mem_cellSaddles hQ) hne.symm
      have hz : (B Q) p = 0 := (B Q).zero_of_le_dist (by
        change 2 * ρ ≤ dist p Q
        have ht := dist_triangle_left P Q p
        dsimp only [ρ] at hball ⊢
        linarith [Real.pi_pos])
      simp [G, hz]
    rw [hsum]
    have hone := (B P).one_of_mem_closedBall hball.le
    simp [G, hone]

private theorem smoothForcing_congr_nhds {lam : ℝ} {P : Plane} {f g : Plane → ℂ}
    (h : f =ᶠ[𝓝 P] g) : smoothForcing lam f =ᶠ[𝓝 P] smoothForcing lam g := by
  obtain ⟨U, he, hU, hmem⟩ := eventually_nhds_iff.mp h
  filter_upwards [hU.mem_nhds hmem] with p hp
  have hv : f =ᶠ[𝓝 p] g := eventually_of_mem (hU.mem_nhds hp) fun q hq ↦ he q hq
  have h₀ := coordPartial_congr_nhds (j := 0) hv
  have h₁ := coordPartial_congr_nhds (j := 1) hv
  change partialX f p = partialX g p at h₀
  change partialY f p = partialY g p at h₁
  simp only [smoothForcing, classicalL0, h₀, h₁, he p hp]

private theorem classicalComplexJet_congr_nhds {P : Plane} {f g : Plane → ℂ}
    (h : f =ᶠ[𝓝 P] g) (w : List (Fin 2)) :
    classicalComplexJet w f =ᶠ[𝓝 P] classicalComplexJet w g := by
  induction w with
  | nil => exact h
  | cons j w ih =>
    obtain ⟨U, he, hU, hmem⟩ := eventually_nhds_iff.mp ih
    filter_upwards [hU.mem_nhds hmem] with p hp
    exact coordPartial_congr_nhds (j := j) (eventually_of_mem (hU.mem_nhds hp) he)

/-- A smooth transport correction removes all the linear jets in the cell
neighbourhood. The forcing remainder has the two weights needed by the
cellwise transport theorem; its derivatives are the specified weak ones. -/
theorem mixed_weighted_forcing_remainder {lam : ℝ} (hlam : lam ≠ 0) {vort : L2}
    (hvort : IsEigenSolution lam vort) (hs : InSector false true vort) :
    ∃ v₀ f₀ : Plane → ℂ, IsTransportPair lam cellNeighbourhood v₀ f₀ ∧
      ContDiff ℝ ∞ v₀ ∧ ContDiff ℝ ∞ f₀ ∧
      MemLp (fun p ↦ (contStream vort p - f₀ p) / (saddleDist p ^ 2 : ℂ)) 2
        (volume.restrict cellSquare) ∧
      ∀ j, MemLp (fun p ↦ (liftL2 (streamPartial j vort) p - coordPartial j f₀ p) /
        (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2 (volume.restrict cellSquare) := by
  classical
  have hjets (P : Plane) (hP : P ∈ saddleSet) : ∃ a : ℂ, ∃ r : ℝ, 0 < r ∧
      ∃ E, HasWeakJetOn 2 (localDisk P r) (fun p ↦ contStream vort p - oddSaddleLinear P a p) E ∧
        ∀ k ≤ 2, RadialJetLp k (3 - k) (localDisk P r) P E := by
    obtain ⟨r, hr, a, ⟨D, hD, hDw⟩, _⟩ := mixed_saddle_jet hlam hvort hs P hP
    have hD' : HasWeakJetOn 2 (localDisk 0 r)
        ((fun p ↦ contStream vort p - oddSaddleLinear P a p) ∘ saddleOrthoChart P) D := by
      convert hD using 1
      funext q
      exact congrArg (contStream vort (saddleOrthoChart P q) - ·)
        (congrFun (oddSaddleLinear_comp P a) q)
    obtain ⟨E, hE, hEw⟩ := saddle_chart_pushforward hP hD'
    exact ⟨a, r, hr, E, hE, fun k hk ↦ hEw k _ (hDw k hk)⟩
  choose a r hr E hE hEw using hjets
  let b (P : Plane) := if hP : P ∈ saddleSet then oddCorrectionCoeff lam P (a P hP) else 0
  obtain ⟨P₀, hP₀, hP₀loc⟩ := exists_smooth_odd_profile b
  let v₀ (p : Plane) := (-Complex.I / (lam : ℂ)) * classicalL0 P₀ p
  let f₀ := smoothForcing lam P₀
  have hU := isOrbitUnion_cellNeighbourhood.1
  obtain ⟨hp, hv₀, hf₀, _, _⟩ := smooth_transport_pair hlam isOrbitUnion_cellNeighbourhood
    isBounded_cellNeighbourhood hP₀
  let J (w : List (Fin 2)) := fun p ↦ streamJet2 vort w p - classicalComplexJet w f₀ p
  have hJ : HasWeakJetOn 2 cellNeighbourhood (fun p ↦ contStream vort p - f₀ p) J :=
    (streamJet2_weak vort _).sub (classicalComplexJet_weak hf₀ 2 _)
  have hw (P : Plane) (hP : P ∈ saddleSet) (hPU : P ∈ cellNeighbourhood) :
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ k ≤ 2, RadialJetLp k (3 - k) (localDisk P ρ) P J := by
    let L := oddSaddleLinear P (a P hP)
    let F := fun p ↦ f₀ p - L p
    have hrU : ∃ ρ > 0, localDisk P ρ ⊆ cellNeighbourhood := by
      obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hPU)
      exact ⟨ρ, hρ, fun p hp ↦ hsub ((dist_le_localRadius P p).trans_lt hp)⟩
    obtain ⟨r₁, hr₁, hr₁U⟩ := hrU
    have hn := smoothForcing_congr_nhds (lam := lam)
      (hP₀loc P (saddle_mem_cellSaddles hP hPU))
    have hnear : F =ᶠ[𝓝 P] fun p ↦ smoothForcing lam
        (oddSaddleLinear P (oddCorrectionCoeff lam P (a P hP))) p - L p := by
      simpa only [F, f₀, b, dite_eq_left hP, Pi.sub_def] using hn.sub (EventuallyEq.rfl (f := L))
    obtain ⟨r₂, hr₂, _, hF, hFw⟩ := exists_radial_classicalJet_flat_memLp isOpen_univ
      (mem_univ P) (hf₀.sub (contDiff_oddSaddleLinear P (a P hP))).contDiffOn 3
      (fun w hw ↦ (classicalComplexJet_congr_nhds hnear w).eq_of_nhds.trans
        (smoothForcing_odd_flat hP hlam (a P hP) w hw))
    let ρ := min (r P hP) (min r₁ r₂)
    have h₁ : localDisk P ρ ⊆ localDisk P (r P hP) :=
      fun p hp ↦ (show localRadius P p < ρ from hp).trans_le (min_le_left _ _)
    have h₂ : localDisk P ρ ⊆ localDisk P r₂ :=
      fun p hp ↦ (show localRadius P p < ρ from hp).trans_le
        ((min_le_right _ _).trans (min_le_right _ _))
    have h₃ : localDisk P ρ ⊆ cellNeighbourhood := fun p hp ↦
      hr₁U ((show localRadius P p < ρ from hp).trans_le
        ((min_le_right _ _).trans (min_le_left _ _)))
    have hR : HasWeakJetOn 2 (localDisk P ρ) (fun p ↦ contStream vort p - f₀ p)
        (fun w p ↦ E P hP w p - classicalComplexJet w F p) := by
      have hF' : HasWeakJetOn 2 (localDisk P ρ) F (fun w ↦ classicalComplexJet w F) :=
        ⟨hF.1, fun w hw j ↦ (hF.2 w (by omega) j).mono h₂⟩
      convert ((hE P hP).mono h₁).sub hF' using 1
      funext p
      dsimp only [F]
      ring
    refine ⟨ρ, lt_min (hr P hP) (lt_min hr₁ hr₂), fun k hk w hlen ↦ ?_⟩
    have he := (hJ.mono h₃).ae_eq (isOpen_localDisk P ρ) hR w (hlen ▸ hk)
    have hEw' := (hEw P hP k hk w hlen).mono_measure (Measure.restrict_mono h₁ le_rfl)
    have hFw' := (hFw k (by omega) w hlen).mono_measure (Measure.restrict_mono h₂ le_rfl)
    apply (hEw'.sub hFw').ae_eq
    filter_upwards [ae_restrict_of_ae he, ae_restrict_mem (isOpen_localDisk P ρ).measurableSet]
      with p hp hpm
    rw [Pi.sub_apply, ← sub_div]
    exact congrArg (fun z : ℂ ↦ z / (localRadius P p ^ (3 - k) : ℂ)) (hp hpm).symm
  have hcell := closure_cellSquare_subset_cellNeighbourhood
  have ho : IsOpen cellSquare := isOpen_cellSquare
  have hc := (isBounded_cellNeighbourhood.subset (subset_closure.trans hcell)).isCompact_closure
  refine ⟨v₀, f₀, hp, hv₀, hf₀, ?_, fun j ↦ ?_⟩
  · have hloc : MemSobolevLocOn 0 cellNeighbourhood (J []) := by
      intro V hV hVc _
      exact memLp_two_restrict_of_continuous ((continuous_contStream vort).sub hf₀.continuous) hV hVc
    have hx := hloc.div_saddleDist_on hU (s := 2) (by norm_num) (fun P hP hPU ↦ by
      obtain ⟨ρ, hρ, hw⟩ := hw P hP hPU
      exact ⟨ρ, hρ, memLp_div_localRadius_rpow (m := 3) (t := 2) (by norm_num)
        (hw 0 (by norm_num) [] rfl)⟩)
    simpa only [J, streamJet2, classicalComplexJet, Real.rpow_eq_pow, Real.rpow_ofNat,
      Complex.ofReal_pow] using
      (show MemLp _ 2 (volume.restrict cellSquare) from hx cellSquare ho hc hcell)
  · have hloc : MemSobolevLocOn 0 cellNeighbourhood (J [j]) := by
      intro V hV hVc _
      exact (memLp_liftL2 _ (hVc.isBounded.subset subset_closure)).sub
        (memLp_two_restrict_of_continuous (contDiff_coordPartial_top j hf₀).continuous hV hVc)
    have hx := hloc.div_saddleDist_on hU (s := 3 / 2) (by norm_num) (fun P hP hPU ↦ by
      obtain ⟨ρ, hρ, hw⟩ := hw P hP hPU
      exact ⟨ρ, hρ, memLp_div_localRadius_rpow (m := 2) (t := 3 / 2) (by norm_num)
        (hw 1 (by norm_num) [j] rfl)⟩)
    exact hx cellSquare ho hc hcell

/-- Mixed eigenfunction vorticity is H¹ on an inward cell collar, with
canonical zero traces on the odd sides. This is a cellwise assertion;
it does not yet glue through the separatrix. -/
theorem mixed_cell_separatrix_h1 {lam : ℝ} (hlam : lam ≠ 0) {vort : L2}
    (hvort : IsEigenSolution lam vort) (hs : InSector false true vort) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ MemSobolevOn 1 (cellSeparatrixStrip ε) (liftL2 vort) ∧
      ∀ σ : Bool, HasCellEdgeTrace (cellSeparatrixStrip ε) 0 σ (liftL2 vort) (fun _ ↦ 0) := by
  obtain ⟨v₀, f₀, hp₀, hv₀, hf₀, hval, hgrad⟩ := mixed_weighted_forcing_remainder hlam hvort hs
  have hp := isTransportPair_contStream hlam hvort isOrbitUnion_cellNeighbourhood
    isBounded_cellNeighbourhood
  have hrem : IsTransportPair lam cellNeighbourhood
      (fun p ↦ liftL2 vort p - v₀ p) (fun p ↦ contStream vort p - f₀ p) := by
    convert hp.add (hp₀.const_mul (-1)) using 1 <;> funext p <;> ring
  have hD (j : Fin 2) : HasWeakPartialOn cellNeighbourhood j
      (fun p ↦ contStream vort p - f₀ p)
      (fun p ↦ liftL2 (streamPartial j vort) p - coordPartial j f₀ p) :=
    ((streamJet2_weak vort cellNeighbourhood).sub
      (classicalComplexJet_weak hf₀ 2 cellNeighbourhood)).2 [] (by simp) j
  obtain ⟨_, r, hr, hrhalf, hH, _⟩ := weighted_transport_h1 hrem isBounded_cellNeighbourhood
    closure_cellSquare_subset_cellNeighbourhood hD hval hgrad
  have hε : 0 < 2 * r := by positivity
  have hsU : cellSeparatrixStrip (2 * r) ⊆ cellNeighbourhood :=
    fun _ hp ↦ closure_cellSquare_subset_cellNeighbourhood (subset_closure hp.1)
  have hc : IsCompact (closure (cellSeparatrixStrip (2 * r))) :=
    (isBounded_cellNeighbourhood.subset hsU).isCompact_closure
  have hV := memSobolevLocOn_of_contDiff 1 univ (hv₀.of_le (by simp))
    (cellSeparatrixStrip (2 * r)) (isOpen_cellSeparatrixStrip _) hc (subset_univ _)
  have hH' : MemSobolevOn 1 (cellSeparatrixStrip (2 * r)) (liftL2 vort) := by
    apply MemSobolevOn.congr_ae (MemSobolevOnWith.add hH hV)
    exact Eventually.of_forall fun p ↦ sub_add_cancel (liftL2 vort p) (v₀ p)
  refine ⟨2 * r, hε, by linarith, hH', fun σ ↦ ?_⟩
  apply transport_zero_edge_trace hp closure_cellSquare_subset_cellNeighbourhood hε hH'
    ((saddle_first_gain hlam hvort).mono_measure (Measure.restrict_mono hsU le_rfl))
    (continuous_contStream vort).continuousOn EventuallyEq.rfl 0 σ
  intro s _
  apply contStream_eq_zero_of_odd_first hs
  change (↑(cellEdgeNormal σ + s) : Real.Angle) + ↑(cellEdgeNormal σ - s) = ↑Real.pi
  rw [← Real.Angle.coe_add]
  cases σ
  · rw [show cellEdgeNormal false + s + (cellEdgeNormal false - s) = -Real.pi by
        simp [cellEdgeNormal]]
    apply Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr
    exact ⟨-1, by push_cast; ring⟩
  · congr 1
    simp [cellEdgeNormal]

end NoEmbeddedEigenvalues
