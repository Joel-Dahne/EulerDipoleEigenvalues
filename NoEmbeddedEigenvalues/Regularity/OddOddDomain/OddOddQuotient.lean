import NoEmbeddedEigenvalues.Transport.WeightedGains.PeriodicTransportGain
import NoEmbeddedEigenvalues.Setup.Derivatives
import NoEmbeddedEigenvalues.Regularity.OddOddDomain.StreamQuotientAssembly
import NoEmbeddedEigenvalues.Analysis.LocalSobolev.EvenGradientHardy
import NoEmbeddedEigenvalues.Virial.OriginalDomain.VirialFourier

/-!
# Minimal odd–odd quotient domain

The sector-specific analytic input is the even H² stream quotient. Coordinate Hardy
and the Poisson equation supply the L² vorticity quotient. Invariant division of weak
transport and the periodic first transport gain then give the exclusion data.

The periodic gain includes passage from the positive cell to the fixed bounded lift
neighbourhood. Its hypothesis is a global torus transport relation, not merely a pair
on that neighbourhood: the latter would not control its boundary saddles.
No separate weighted corner remainder of the stream quotient is used.

For the stream construction, bounded radial powers convert the weighted third jet
of `ψ - a * Ψ` to an ordinary H³ jet on each saddle disk. An affine pullback mixes
all derivative indices; merely composing the Cartesian jet entries is not enough.
Double division and point removal use the same punctured second jet. Remove the
point for `V = (ψ - a * Ψ) / (u * v)` first, then shrink before multiplication by
`m⁻¹`. At regular edges the second chart coordinate is normal, as in `odd_h3_division`.
Local representatives agree a.e. with one periodic raw quotient. Values assigned to
that quotient on the separatrix are not the values of its continuous H² representative.
Local Sobolev gluing on the lift is separate from periodization. Once the lift is
locally H² everywhere, one compact cutoff with periodized value one suffices for
passage to the torus; it can be built from the existing unit-period angular partition.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set

/-- Dividing odd–odd data by the dipole gives even data. Only the a.e.
multiplication identity is needed, not quotient regularity or the eigen-equation. -/
theorem InSector.even_dipole_quotient {ψ φ : L2} (hs : InSector false false ψ)
    (hψ : ∀ᵐ t, ψ t = (Ψ t : ℂ) * φ t) : InSector true true φ := by
  have hnull := ae_Ψ_ne_zero
  have href {T : Torus → Torus} (hT : MeasurePreserving T)
      (hΨT : ∀ t, Ψ (T t) = -Ψ t) (hψT : pullback T hT ψ = -ψ) :
      pullback T hT φ = φ := by
    apply Lp.ext
    have hraw := Lp.coeFn_compMeasurePreserving φ hT
    change (pullback T hT φ : Torus → ℂ) =ᵐ[volume] (fun t ↦ φ (T t)) at hraw
    filter_upwards [hraw, ae_comp_of_pullback_eq hψT, Lp.coeFn_neg ψ, hψ,
      hT.quasiMeasurePreserving.ae hψ, hnull] with t ht hst hnt hpt hspt hn
    rw [ht]
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hn)
    have heq : -(Ψ t : ℂ) * φ (T t) = -((Ψ t : ℂ) * φ t) := by
      simpa only [hΨT t, Complex.ofReal_neg, hst, hnt, Pi.neg_apply, hpt] using hspt.symm
    simpa only [neg_mul, neg_inj] using heq
  constructor
  · simpa [paritySign, reflect₁, CharacterSymmetry.action, symmetry₁] using
      href measurePreserving_S₁ (fun t ↦ congrFun Ψ_comp_S₁ t)
        (by simpa [paritySign, reflect₁, CharacterSymmetry.action, symmetry₁] using hs.1)
  · simpa [paritySign, reflect₂, CharacterSymmetry.action, symmetry₂] using
      href measurePreserving_S₂ (fun t ↦ congrFun Ψ_comp_S₂ t)
        (by simpa [paritySign, reflect₂, CharacterSymmetry.action, symmetry₂] using hs.2)

/-- Even H² stream quotient (`prop:dd-stream-quotient-h2`). -/
theorem dd_stream_quotient_h2 {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ φ : L2, MemSobolev 2 φ ∧ InSector true true φ ∧
      ∀ᵐ t, invLap ω t = (Ψ t : ℂ) * φ t := by
  obtain ⟨φ, hφ, hψ⟩ := exists_h2_stream_quotient hlam hω hs
  exact ⟨φ, hφ, hs.invLap.even_dipole_quotient hψ, hψ⟩

/-- Apply the Fourier product rule twice before passing to raw representatives. -/
private theorem dipole_laplacian_expansion {φ ψ ζ : L2} (hφ : MemSobolev 2 φ)
    (hψ : ∀ᵐ t, ψ t = (Ψ t : ℂ) * φ t) (hΔ : HasFourierLaplacian ψ ζ) :
    ∃ τ dx dy : L2, HasFourierPartial 0 φ dx ∧ HasFourierPartial 1 φ dy ∧
      ∀ᵐ p, liftL2 ζ p =
        (dipoleLift p : ℂ) * (liftL2 τ p - liftL2 φ p) -
          2 * ((Real.sin p.1 : ℂ) * liftL2 dx p + (Real.sin p.2 : ℂ) * liftL2 dy p) := by
  have h1 := hφ.mono (by norm_num : (1 : ℝ) ≤ 2)
  obtain ⟨dx, hdx⟩ := h1.exists_hasFourierPartial 0
  obtain ⟨dy, hdy⟩ := h1.exists_hasFourierPartial 1
  have hφ' : MemSobolev ((1 : ℝ) + 1) φ := by norm_num; exact hφ
  obtain ⟨dxx, hdxx⟩ := (hφ'.of_hasFourierPartial hdx).exists_hasFourierPartial 0
  obtain ⟨dyy, hdyy⟩ := (hφ'.of_hasFourierPartial hdy).exists_hasFourierPartial 1
  let s : ℝ × ℝ → ℂ := fun p ↦ (dipoleLift p : ℂ)
  have hsR : ContDiff ℝ 2 dipoleLift := by unfold dipoleLift; fun_prop
  have hs2 : ContDiff ℝ 2 s := Complex.ofRealCLM.contDiff.comp hsR
  have hs1 : ContDiff ℝ 1 s := hs2.of_le (by norm_num)
  have hp : IsPeriodicLift s := by
    intro p
    dsimp [s, dipoleLift]
    simp [Real.cos_add, Real.cos_two_pi, Real.sin_two_pi]
  have hx1 : ContDiff ℝ 1 (partialX s) := contDiff_partialX hs2
  have hy1 : ContDiff ℝ 1 (partialY s) := contDiff_partialY hs2
  let c := torusFun hs1.continuous hp
  let cx := torusFun hx1.continuous hp.partialX
  let cy := torusFun hy1.continuous hp.partialY
  let cxx := torusFun (continuous_partialX_of_contDiff hx1) hp.partialX.partialX
  let cyy := torusFun (continuous_partialY_of_contDiff hy1) hp.partialY.partialY
  have hc (t : Torus) : c t = (Ψ t : ℂ) := by
    obtain ⟨p, rfl⟩ := torusProj_surjective t
    exact (torusOfLift_torusProj hp p).trans (congrArg Complex.ofReal (Ψ_torusProj p).symm)
  have hcp : ψ = mulL2 c φ := by
    apply Lp.ext
    filter_upwards [hψ, mulL2_ae c φ] with t h ht
    rw [h, ht, hc]
  have hcx : HasClassicalPartial 0 c cx := hasClassicalPartial_torusFun_x hs1 hp
  have hcy : HasClassicalPartial 1 c cy := hasClassicalPartial_torusFun_y hs1 hp
  have hcxx : HasClassicalPartial 0 cx cxx := hasClassicalPartial_torusFun_x hx1 hp.partialX
  have hcyy : HasClassicalPartial 1 cy cyy := hasClassicalPartial_torusFun_y hy1 hp.partialY
  have hprod {j : Fin 2} {d dd : L2} {dc ddc : C(Torus, ℂ)}
      (hd : HasFourierPartial j φ d) (hdd : HasFourierPartial j d dd)
      (hc' : HasClassicalPartial j c dc) (hdc : HasClassicalPartial j dc ddc) :
      HasFourierSecondPartial j j ψ
        ((mulL2 ddc φ + mulL2 dc d) + (mulL2 dc d + mulL2 c dd)) := by
    rw [hcp]
    exact (hasFourierPartial_iff_second (hasFourierPartial_mulL2 hc' hd)).mp
      ((hasFourierPartial_mulL2 hdc hd).add (hasFourierPartial_mulL2 hc' hdd))
  let X := (mulL2 cxx φ + mulL2 cx dx) + (mulL2 cx dx + mulL2 c dxx)
  let Y := (mulL2 cyy φ + mulL2 cy dy) + (mulL2 cy dy + mulL2 c dyy)
  have hXY : HasFourierLaplacian ψ (X + Y) :=
    hasFourierLaplacian_of_second (hprod hdx hdxx hcx hcxx) (hprod hdy hdyy hcy hcyy)
  have he : ζ = X + Y := fourierCoeff_ext fun k ↦ (hΔ k).trans (hXY k).symm
  have hraw (d dd : L2) (dc ddc : C(Torus, ℂ)) :
      ((mulL2 ddc φ + mulL2 dc d) + (mulL2 dc d + mulL2 c dd) : L2) =ᵐ[volume]
        fun t ↦ ddc t * φ t + 2 * dc t * d t + c t * dd t := by
    filter_upwards [Lp.coeFn_add (mulL2 ddc φ + mulL2 dc d) (mulL2 dc d + mulL2 c dd),
      Lp.coeFn_add (mulL2 ddc φ) (mulL2 dc d), Lp.coeFn_add (mulL2 dc d) (mulL2 c dd),
      mulL2_ae ddc φ, mulL2_ae dc d, mulL2_ae c dd] with t h ha hb h₁ h₂ h₃
    simp only [h, Pi.add_apply, ha, hb, h₁, h₂, h₃]
    ring
  have hsx : partialX s = fun p ↦ -(Real.sin p.1 : ℂ) := by
    funext p
    rw [partialX_ofReal (show Differentiable ℝ dipoleLift by unfold dipoleLift; fun_prop),
      partialX_dipoleLift]
    exact Complex.ofReal_neg _
  have hsy : partialY s = fun p ↦ -(Real.sin p.2 : ℂ) := by
    funext p
    rw [partialY_ofReal (show Differentiable ℝ dipoleLift by unfold dipoleLift; fun_prop),
      partialY_dipoleLift]
    exact Complex.ofReal_neg _
  have hss (p : ℝ × ℝ) : partialX (partialX s) p + partialY (partialY s) p = -s p := by
    have hd := hsR.differentiable (by norm_num)
    have hdx := (contDiff_partialX hsR).differentiable (by norm_num)
    have hdy := (contDiff_partialY hsR).differentiable (by norm_num)
    rw [show partialX s = fun p ↦ ((partialX dipoleLift p : ℝ) : ℂ) from
          partialX_ofReal hd,
        show partialY s = fun p ↦ ((partialY dipoleLift p : ℝ) : ℂ) from
          partialY_ofReal hd,
        partialX_ofReal hdx, partialY_ofReal hdy]
    simpa only [s, Complex.ofReal_neg, Complex.ofReal_add, laplacian] using
      congrArg Complex.ofReal (laplacian_dipoleLift p)
  refine ⟨dxx + dyy, dx, dy, hdx, hdy, ?_⟩
  rw [he]
  filter_upwards [liftL2_add_ae X Y, liftL2_add_ae dxx dyy,
    ae_torusProj (hraw dx dxx cx cxx), ae_torusProj (hraw dy dyy cy cyy)]
    with p h hx hy hz
  rw [h, hx]
  change liftL2 X p = _ at hy
  change liftL2 Y p = _ at hz
  rw [hy, hz, hc, Ψ_torusProj]
  have hx' : cx (torusProj p) = -(Real.sin p.1 : ℂ) :=
    (torusOfLift_torusProj hp.partialX p).trans (congrFun hsx p)
  have hy' : cy (torusProj p) = -(Real.sin p.2 : ℂ) :=
    (torusOfLift_torusProj hp.partialY p).trans (congrFun hsy p)
  have hsum : cxx (torusProj p) + cyy (torusProj p) = -(dipoleLift p : ℂ) :=
    (congrArg₂ (· + ·) (torusOfLift_torusProj hp.partialX.partialX p)
      (torusOfLift_torusProj hp.partialY.partialY p)).trans (hss p)
  rw [hx', hy']
  simp only [liftL2]
  linear_combination (φ (torusProj p)) * hsum

/-- The singular term is a bounded combination of the two Hardy quotients. -/
private theorem memLp_div_dipole_gradient {φ dx dy : L2} (hφ : MemSobolev 2 φ)
    (hs : InSector true true φ) (hx : HasFourierPartial 0 φ dx)
    (hy : HasFourierPartial 1 φ dy) :
    MemLp (fun p ↦ (2 * ((Real.sin p.1 : ℂ) * liftL2 dx p +
      (Real.sin p.2 : ℂ) * liftL2 dy p)) / (dipoleLift p : ℂ)) 2
      (volume.restrict cellSquare) := by
  obtain ⟨mA, mB⟩ := even_h2_diagonal_gradient_division hφ hs hx hy
  have mul_sin (f : ℝ × ℝ → ℂ) (hf : MemLp f 2 (volume.restrict cellSquare))
      (a : ℝ × ℝ → ℝ) (ha : Continuous a) :
      MemLp (fun p ↦ (Real.sin (a p) : ℂ) * f p) 2 (volume.restrict cellSquare) := by
    apply hf.of_le_mul (c := 1)
      ((Complex.continuous_ofReal.comp (Real.continuous_sin.comp ha)).aestronglyMeasurable.mul
        hf.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun p ↦ by
      change ‖(Real.sin (a p) : ℂ) * f p‖ ≤ 1 * ‖f p‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, one_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)
  have hc : Continuous diagCoord := by unfold diagCoord; fun_prop
  apply ((mul_sin _ mA _ hc.fst).add (mul_sin _ mB _ hc.snd)).ae_eq
  filter_upwards [ae_restrict_mem isOpen_cellSquare.measurableSet] with p hp
  let a := (diagCoord p).1
  let b := (diagCoord p).2
  have hca : (Real.cos a : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.cos_pos_of_mem_Ioo (abs_lt.mp hp.1)).ne'
  have hcb : (Real.cos b : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.cos_pos_of_mem_Ioo (abs_lt.mp hp.2)).ne'
  have hx' : p.1 = a + b := by dsimp [a, b, diagCoord]; ring
  have hy' : p.2 = a - b := by dsimp [a, b, diagCoord]; ring
  have hs' : dipoleLift p = 2 * Real.cos a * Real.cos b := dipoleLift_eq_diag p
  change (Real.sin a : ℂ) * ((liftL2 dx p + liftL2 dy p) / (Real.cos a : ℂ)) +
    (Real.sin b : ℂ) * ((liftL2 dx p - liftL2 dy p) / (Real.cos b : ℂ)) =
    (2 * ((Real.sin p.1 : ℂ) * liftL2 dx p + (Real.sin p.2 : ℂ) * liftL2 dy p)) /
      (dipoleLift p : ℂ)
  rw [hs', hx', hy', Real.sin_add, Real.sin_sub]
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
  field_simp
  ring

/-- Reflection transfers a positive-cell norm of the divided odd datum to the torus. -/
private theorem memLp_div_dipole_of_odd_cell {ζ : L2} (hodd : reflect₁ ζ = -ζ)
    (hcell : MemLp (fun p ↦ liftL2 ζ p / (dipoleLift p : ℂ)) 2
      (volume.restrict cellSquare)) :
    MemLp (fun t ↦ ζ t / (Ψ t : ℂ)) 2 volume := by
  let q := fun t ↦ ζ t / (Ψ t : ℂ)
  have hΨ : Continuous Ψ :=
    (Real.Angle.continuous_cos.comp continuous_fst).add
      (Real.Angle.continuous_cos.comp continuous_snd)
  have hpos : MeasurableSet positiveCell := (isOpen_lt continuous_const hΨ).measurableSet
  have hrep : torusRep ⁻¹' cellSquare = positiveCell := by
    ext t
    change torusRep t ∈ cellSquare ↔ t ∈ positiveCell
    constructor
    · intro ht
      simpa only [torusProj_torusRep] using torusProj_mem_positiveCell ht
    · intro ht
      apply mem_cellSquare_of_mem_periodBox (torusRep_mem t)
      rw [← Ψ_torusProj, torusProj_torusRep]
      exact ht
  have hm := measurePreserving_torusRep.restrict_preimage isOpen_cellSquare.measurableSet
  rw [hrep, Measure.restrict_restrict_of_subset cellSquare_subset_periodBox] at hm
  have hq : MemLp q 2 (volume.restrict positiveCell) := by
    apply (hcell.comp_measurePreserving hm).ae_eq
    exact Filter.Eventually.of_forall fun t ↦ by
      simp only [Function.comp_apply, liftL2, ← Ψ_torusProj, torusProj_torusRep, q]
  let P := positiveCell.indicator q
  have hP : MemLp P 2 volume := (memLp_indicator_iff_restrict hpos).mpr hq
  have hsym : ∀ᵐ t, q (S₁ t) = q t := by
    filter_upwards [ae_comp_of_pullback_eq (T := S₁) (hT := measurePreserving_S₁) hodd,
      Lp.coeFn_neg ζ] with t hs hn
    have hS : Ψ (S₁ t) = -Ψ t := congrFun Ψ_comp_S₁ t
    simp only [q, hs, hn, Pi.neg_apply, hS, Complex.ofReal_neg, neg_div_neg_eq]
  apply (hP.add (hP.comp_measurePreserving measurePreserving_S₁)).ae_eq
  filter_upwards [hsym, ae_Ψ_ne_zero] with t ht hn
  change P t + P (S₁ t) = q t
  dsimp only [P]
  have hS : Ψ (S₁ t) = -Ψ t := congrFun Ψ_comp_S₁ t
  rcases lt_or_gt_of_ne hn with hneg | hpos'
  · have h₁ : t ∉ positiveCell := not_lt_of_gt hneg
    have h₂ : S₁ t ∈ positiveCell := by change 0 < Ψ (S₁ t); rw [hS]; linarith
    rw [indicator_of_notMem h₁, indicator_of_mem h₂, zero_add, ht]
  · have h₁ : t ∈ positiveCell := hpos'
    have h₂ : S₁ t ∉ positiveCell := by change ¬0 < Ψ (S₁ t); rw [hS]; linarith
    rw [indicator_of_mem h₁, indicator_of_notMem h₂, add_zero]

/-- Coordinate Hardy controls the divided Laplacian of an even H² function
(`lem:even-h2-dipole-laplacian`). The Laplacian is specified by its Fourier relation;
no classical second derivative of an arbitrary L² representative is used. -/
theorem even_h2_dipole_laplacian {φ ψ ζ : L2} (hφ : MemSobolev 2 φ)
    (hs : InSector true true φ) (hψ : ∀ᵐ t, ψ t = (Ψ t : ℂ) * φ t)
    (hΔ : HasFourierLaplacian ψ ζ) :
    ∃ ν : L2, ∀ᵐ t, ζ t = (Ψ t : ℂ) * ν t := by
  obtain ⟨τ, dx, dy, hx, hy, he⟩ := dipole_laplacian_expansion hφ hψ hΔ
  have hnorm (u : L2) : MemLp (liftL2 u) 2 (volume.restrict cellSquare) :=
    (memLp_liftL2_periodBox u).mono_measure
      (Measure.restrict_mono cellSquare_subset_periodBox le_rfl)
  have hcell : MemLp (fun p ↦ liftL2 ζ p / (dipoleLift p : ℂ)) 2
      (volume.restrict cellSquare) := by
    apply (((hnorm τ).sub (hnorm φ)).sub (memLp_div_dipole_gradient hφ hs hx hy)).ae_eq
    filter_upwards [ae_restrict_of_ae he, ae_restrict_mem isOpen_cellSquare.measurableSet]
      with p hp hmem
    have hne : (dipoleLift p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (show 0 < dipoleLift p by
        simpa only [positiveCell, mem_ofPred_eq, Ψ_torusProj] using
          torusProj_mem_positiveCell hmem).ne'
    simp only [Pi.sub_apply, hp, sub_div, mul_div_cancel_left₀ _ hne]
  have hφR : reflect₁ φ = φ := by
    simpa only [paritySign, ite_true, one_smul] using hs.1
  have hψR : reflect₁ ψ = -ψ := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving ψ measurePreserving_S₁,
      ae_comp_of_pullback_eq (T := S₁) (hT := measurePreserving_S₁) hφR,
      measurePreserving_S₁.quasiMeasurePreserving.ae hψ, hψ, Lp.coeFn_neg ψ]
      with t h₀ h₁ h₂ h₃ h₄
    change (reflect₁ ψ : Torus → ℂ) t = ψ (S₁ t) at h₀
    have hS : Ψ (S₁ t) = -Ψ t := congrFun Ψ_comp_S₁ t
    rw [h₀, h₄, Pi.neg_apply, h₂, h₁, h₃, hS, Complex.ofReal_neg, neg_mul]
  have hΔR := symmetry₁.hasFourierLaplacian hΔ
  change HasFourierLaplacian (reflect₁ ψ) (reflect₁ ζ) at hΔR
  rw [hψR] at hΔR
  have hζR : reflect₁ ζ = -ζ := by
    apply fourierCoeff_ext
    intro k
    rw [hΔR k]
    simp only [show -ψ = (-1 : ℂ) • ψ by simp, show -ζ = (-1 : ℂ) • ζ by simp,
      fourierCoeff_smul, hΔ k]
    ring
  let q := fun t ↦ ζ t / (Ψ t : ℂ)
  have hq : MemLp q 2 volume := memLp_div_dipole_of_odd_cell hζR hcell
  refine ⟨hq.toLp q, ?_⟩
  filter_upwards [hq.coeFn_toLp, ae_Ψ_ne_zero] with t ht hn
  rw [ht]
  exact (mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hn)).symm

/-- The vorticity quotient follows from the stream quotient and the Poisson equation
(`lem:dd-vorticity-quotient-l2`), without a separate angular Hardy estimate on ω. -/
theorem dd_vorticity_quotient_l2 {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∃ ν : L2, ∀ᵐ t, ω t = (Ψ t : ℂ) * ν t := by
  obtain ⟨φ, hφ, hsφ, hψ⟩ := dd_stream_quotient_h2 hlam hω hs
  exact even_h2_dipole_laplacian hφ hsφ hψ (hasFourierLaplacian_invLap ω hω.1)

open Filter Complex in
open scoped Topology ContDiff in
/-- Smooth functions of the dipole are invariant C¹ torus multipliers. -/
private theorem dipole_multiplier (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    ∃ M Mx My : C(Torus, ℂ),
      (∀ t, M t = (f (Ψ t) : ℂ)) ∧ HasClassicalPartial 0 M Mx ∧
      HasClassicalPartial 1 M My ∧
      (∀ t, sinYTorus t * Mx t - sinXTorus t * My t = 0) := by
  have hc : Continuous Ψ :=
    (Real.Angle.continuous_cos.comp continuous_fst).add
      (Real.Angle.continuous_cos.comp continuous_snd)
  let M : C(Torus, ℂ) := ⟨fun t ↦ (f (Ψ t) : ℂ), by fun_prop⟩
  let D : C(Torus, ℂ) := ⟨fun t ↦ ((deriv f (Ψ t) : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (hf.continuous_deriv_one.comp hc)⟩
  refine ⟨M, -sinXTorus * D, -sinYTorus * D, fun _ ↦ rfl, ?_, ?_, ?_⟩
  · intro p t
    rcases p with ⟨x, y⟩
    induction x using Real.Angle.induction_on with | h x =>
      induction y using Real.Angle.induction_on with | h y =>
        have hd := ((hf.differentiable (by simp) _).hasDerivAt.comp t
          ((Real.hasDerivAt_cos t).add_const (Real.cos y))).ofReal_comp
        convert hd using 1 <;>
          simp [M, D, coordinateLine, Ψ, sinXTorus_apply, Real.Angle.cos_coe,
            Real.Angle.sin_coe]
        ring
  · intro p t
    rcases p with ⟨x, y⟩
    induction x using Real.Angle.induction_on with | h x =>
      induction y using Real.Angle.induction_on with | h y =>
        have hd := ((hf.differentiable (by simp) _).hasDerivAt.comp t
          ((Real.hasDerivAt_cos t).const_add (Real.cos x))).ofReal_comp
        convert hd using 1 <;>
          simp [M, D, coordinateLine, Ψ, sinYTorus_apply, Real.Angle.cos_coe,
            Real.Angle.sin_coe]
        ring
  · intro t
    simp only [ContinuousMap.mul_apply, ContinuousMap.neg_apply]
    ring

/-- Periodic weak invariant division (`cor:dd-quotient-transport-periodic`).
Only the L² quotients and their multiplication identities are assumed; neither H¹
regularity of ν nor corner weights are hypotheses. -/
theorem dd_quotient_transport {lam : ℝ} {ω ψ ν φ : L2}
    (h : HasL0 (ω + ψ) ((Complex.I * lam) • ω))
    (hψ : ∀ᵐ t, ψ t = (Ψ t : ℂ) * φ t)
    (hω : ∀ᵐ t, ω t = (Ψ t : ℂ) * ν t) :
    HasL0 (ν + φ) ((Complex.I * lam) • ν) := by
  have hc : Continuous Ψ :=
    (Real.Angle.continuous_cos.comp continuous_fst).add
      (Real.Angle.continuous_cos.comp continuous_snd)
  -- Establish the divided identity against arbitrary C¹ torus tests.
  have htest {Φ Φx Φy : C(Torus, ℂ)}
      (hx : HasClassicalPartial 0 Φ Φx) (hy : HasClassicalPartial 1 Φ Φy) :
      (∫ t, (Complex.I * lam) * ν t * Φ t) =
        -∫ t, (ν t + φ t) * (sinYTorus t * Φx t - sinXTorus t * Φy t) := by
    let LΦ : C(Torus, ℂ) := sinYTorus * Φx - sinXTorus * Φy
    let F : Torus → ℂ := fun t ↦ (Complex.I * lam) * ν t * Φ t
    let G : Torus → ℂ := fun t ↦ (ν t + φ t) * LΦ t
    have hF : Integrable F := by
      simpa only [F, mul_assoc] using
        (integrable_mul_continuous ν Φ).const_mul (Complex.I * lam)
    have hG : Integrable G := by
      exact ((integrable_mul_continuous ν LΦ).add
        (integrable_mul_continuous φ LΦ)).congr (Filter.Eventually.of_forall fun t ↦ by
          simp only [G, add_mul, Pi.add_apply])
    let ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
    have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
    let χ : ℕ → Torus → ℂ := fun n t ↦ (Ψ t ^ 2 / (Ψ t ^ 2 + ε n) : ℝ)
    have hχc (n : ℕ) : Continuous (χ n) := by
      exact Complex.continuous_ofReal.comp ((hc.pow 2).div
        ((hc.pow 2).add continuous_const) fun t ↦ ne_of_gt (by positivity))
    have hχbound (n : ℕ) (t : Torus) : ‖χ n t‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (div_le_one (by positivity)).2 (by linarith [hε n])
    have hχlim : ∀ᵐ t, Filter.Tendsto (fun n ↦ χ n t) Filter.atTop (nhds 1) := by
      filter_upwards [ae_Ψ_ne_zero] with t ht
      have he : Filter.Tendsto ε Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hd := (tendsto_const_nhds (x := Ψ t ^ 2)).div (tendsto_const_nhds.add he)
        (show Ψ t ^ 2 + 0 ≠ 0 by simpa using pow_ne_zero 2 ht)
      simpa only [χ, Function.comp_def, Pi.div_apply, add_zero,
        div_self (pow_ne_zero 2 ht), Complex.ofReal_one] using
        Complex.continuous_ofReal.continuousAt.tendsto.comp hd
    have hlim (J : Torus → ℂ) (hJ : Integrable J) :
        Filter.Tendsto (fun n ↦ ∫ t, χ n t * J t) Filter.atTop (nhds (∫ t, J t)) := by
      apply tendsto_integral_of_dominated_convergence (fun t ↦ ‖J t‖)
      · intro n
        exact (hχc n).aestronglyMeasurable.mul hJ.aestronglyMeasurable
      · exact hJ.norm
      · intro n
        exact Filter.Eventually.of_forall fun t ↦ by
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (hχbound n t)
      · filter_upwards [hχlim] with t ht
        simpa using ht.mul_const (J t)
    have heq (n : ℕ) : (∫ t, χ n t * F t) = -∫ t, χ n t * G t := by
      let f : ℝ → ℝ := fun s ↦ s / (s ^ 2 + ε n)
      have hf : ContDiff ℝ 1 f :=
        contDiff_id.div ((contDiff_id.pow 2).add contDiff_const)
          (fun s ↦ ne_of_gt (by positivity))
      obtain ⟨M, Mx, My, hM, hMx, hMy, hM0⟩ := dipole_multiplier f hf
      have hw := h.integral_mul_eq (hMx.mul hx) (hMy.mul hy)
      have hcanc (t : Torus) : M t * (Ψ t : ℂ) = χ n t := by
        rw [hM]
        dsimp [f, χ]
        push_cast
        ring
      have hleft : (∫ t, ((Complex.I * lam) • ω : L2) t * (M * Φ) t) =
          ∫ t, χ n t * F t := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul (Complex.I * lam) ω, hω] with t ht hωt
        simp only [ht, Pi.smul_apply, smul_eq_mul, ContinuousMap.mul_apply, hωt, F]
        linear_combination ((Complex.I * lam) * ν t * Φ t) * hcanc t
      have hright : (∫ t, (ω + ψ : L2) t *
          (sinYTorus t * (Mx * Φ + M * Φx) t -
            sinXTorus t * (My * Φ + M * Φy) t)) = ∫ t, χ n t * G t := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add ω ψ, hω, hψ] with t ht hωt hψt
        simp only [ht, Pi.add_apply, hωt, hψt, ContinuousMap.add_apply,
          ContinuousMap.mul_apply, G, LΦ, ContinuousMap.sub_apply]
        linear_combination (Ψ t : ℂ) * (ν t + φ t) * Φ t * hM0 t +
          (ν t + φ t) * (sinYTorus t * Φx t - sinXTorus t * Φy t) * hcanc t
      simpa only [hleft, hright] using hw
    exact tendsto_nhds_unique (hlim F hF) (((hlim G hG).neg).congr
      (fun n ↦ (heq n).symm))
  intro k
  have hw := htest (classicalPartial_char 0 k).conj (classicalPartial_char 1 k).conj
  rw [L2.inner_def, L2.inner_def]
  convert hw using 1
  · apply integral_congr_ae
    filter_upwards [charLp_ae_eq k, Lp.coeFn_smul (Complex.I * lam) ν] with t ht hs
    simp [ht, hs, RCLike.inner_apply]
  · congr 1
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume (L0char k),
      Lp.coeFn_add ν φ] with t ht ha
    rw [show (L0charLp k : Torus → ℂ) t = L0char k t from ht, ha]
    simp [Pi.add_apply, RCLike.inner_apply, L0char, sinYTorus_apply, sinXTorus_apply,
      frequencyComponent, mul_comm, mul_left_comm]
    ring

/-- Quotient conclusions used by the final exclusion. Weighted corner remainders are
    deliberately not part of this interface. -/
structure DDQuotientData (lam : ℝ) (ω : L2) where
  phi : L2
  nu : L2
  regular : MemSobolev 2 phi
  even : InSector true true phi
  stream_eq : ∀ᵐ t, invLap ω t = (Ψ t : ℂ) * phi t
  vorticity_eq : ∀ᵐ t, ω t = (Ψ t : ℂ) * nu t
  transport : IsTransportPair lam cellNeighbourhood (liftL2 nu)
    (fun p ↦ continuousRep phi (torusProj p))
  weighted_nu : MemLp (fun p ↦ liftL2 nu p / (saddleDist p : ℂ)) 2
    (volume.restrict cellNeighbourhood)

/-- Existence of the minimal quotient data consumed by exclusion
    (`cor:dd-exclusion-domain`), without the stronger corner-jet conclusions. -/
theorem dd_exclusion_domain {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    Nonempty (DDQuotientData lam ω) := by
  obtain ⟨φ, hφ, hsφ, hψ⟩ := dd_stream_quotient_h2 hlam hω hs
  obtain ⟨ν, hν⟩ :=
    even_h2_dipole_laplacian hφ hsφ hψ (hasFourierLaplacian_invLap ω hω.1)
  have ht := dd_quotient_transport hω.2 hψ hν
  exact ⟨{
    phi := φ
    nu := ν
    regular := hφ
    even := hsφ
    stream_eq := hψ
    vorticity_eq := hν
    transport := isTransportPair_continuousRep hlam hφ ht
      isOrbitUnion_cellNeighbourhood isBounded_cellNeighbourhood
    weighted_nu := transport_first_gain_periodic hlam hφ ht }⟩

end NoEmbeddedEigenvalues
