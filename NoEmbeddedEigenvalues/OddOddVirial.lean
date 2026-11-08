import NoEmbeddedEigenvalues.OddOddQuotientEquations
import NoEmbeddedEigenvalues.SobolevApproximation

/-!
# Weighted odd–odd virial interfaces

Classical differential expressions are used only for smooth functions. The quotient
Poisson equation is instead tested weakly, with specified Fourier first derivatives.
The annular and truncated virials use the original eigenfunction quotients on the
open cell and arbitrary weak derivative witnesses there: global quotient existence
is not a hypothesis. Level parameters here are `s = ε`, so orbit integrals use `ε/2`.

The existing `normalDeriv` points out of the positive superlevel cell. Here the
weighted virial uses the inward normal `∇Ψ/|∇Ψ|`, so its linear normal term must
use the opposite sign; the quadratic energies are unaffected.

The gradient limits allow a common null set of exceptional levels. In contrast,
`OddOddRenormalizedBulk` assembles a full positive-level bulk limit; no all-level
vorticity pairing limit is asserted. Supplied-data bridges identify the raw local quotients a.e.,
rescale exceptional levels by `ε = 2h`, and split the boundary integral using coarea.

Positive truncations need only smooth local division of the original stream, not
existence of global quotient data. Weak-derivative uniqueness gives square integrability
for arbitrary witnesses. Bounded bulk coefficients and a Cauchy–Schwarz center-flux
estimate allow the annular identity to include the center by dominated convergence.
Measurable versions and null hulls transfer these estimates to the given witnesses.

The weighted differential algebra is pointwise on the regular cell. The annular
extraction takes a weak cutoff identity as input, then obtains one exceptional set
for both endpoints by coarea and du Bois–Reymond. The planar boundary density
identifies each level term directly, without splitting its summands.
The weak Green identity, pointwise boundary-flux identification, weak cutoff
identity and annular assembly are separate interfaces. For smooth compactly supported
functions, the annular cutoff flux extends to a globally C¹ compactly supported
field. Its divergence has zero integral; the cutoff generator's half-density
correction then gives the smooth weighted Green identity.
Multiplication back by Ψ identifies supplied weak quotient gradients with Fourier
stream derivatives, giving half-density conjugation without classical raw derivatives.

The weak weighted operator is identified algebraically from any specified second
weak jet by testing its weighted divergence. Bounded coefficient multipliers then
carry strong L² jet convergence to strong L² convergence of the operator values
on precompact cell patches, including patches through the elliptic center.
For weak Green, a compact regular patch contains the cutoff support. On that patch,
all four integrands are finite bounded-coefficient quadratic forms in the value,
forcing and two weak gradients; L² product stability passes the smooth identity
to the supplied representatives.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter Topology

private theorem contDiff_ddWeight_complex :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p ↦ (ddWeight p : ℂ)) := by
  have hreal : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ddWeight := by
    unfold ddWeight dipoleLift
    fun_prop
  exact Complex.ofRealCLM.contDiff.comp hreal

/-- The weighted operator evaluated algebraically on a specified second-order jet.
    No classical derivative is taken of any jet representative. -/
def ddJetOperator (D : List (Fin 2) → ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  D [] p -
    (coordPartial 0 (fun q ↦ (ddWeight q : ℂ)) p * D [0] p +
      (ddWeight p : ℂ) * D [0, 0] p +
      (coordPartial 1 (fun q ↦ (ddWeight q : ℂ)) p * D [1] p +
        (ddWeight p : ℂ) * D [1, 1] p)) / (ddWeight p : ℂ)

/-- A weak realization of the weighted operator agrees with its algebraic jet
    expression on each open patch. Only weak derivative uniqueness is used;
    neither a derivative of the forcing nor smooth density is required. -/
theorem HasDDOperator.ae_eq_jet {u e ux uy : ℝ × ℝ → ℂ}
    (hop : HasDDOperator u e ux uy) {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (hVU : V ⊆ cellSquare)
    {D : List (Fin 2) → ℝ × ℝ → ℂ} (hD : HasWeakJetOn 2 V u D) :
    ∀ᵐ p, p ∈ V →
      ux p = D [0] p ∧ uy p = D [1] p ∧ e p = ddJetOperator D p := by
  have hx : HasWeakPartialOn V 0 u (D [0]) := by
    simpa only [hD.1] using hD.2 [] (by simp) 0
  have hy : HasWeakPartialOn V 1 u (D [1]) := by
    simpa only [hD.1] using hD.2 [] (by simp) 1
  have hux := (hop.1.mono hVU).ae_eq hV hx
  have huy := (hop.2.1.mono hVU).ae_eq hV hy
  have hμ := contDiff_ddWeight_complex
  let a := fun p ↦ coordPartial 0 (fun q ↦ (ddWeight q : ℂ)) p * D [0] p +
    (ddWeight p : ℂ) * D [0, 0] p
  let b := fun p ↦ coordPartial 1 (fun q ↦ (ddWeight q : ℂ)) p * D [1] p +
    (ddWeight p : ℂ) * D [1, 1] p
  have ha : HasWeakPartialOn V 0 (fun p ↦ (ddWeight p : ℂ) * D [0] p) a :=
    (hD.2 [0] (by simp) 0).mul_smooth hV hμ
  have hb : HasWeakPartialOn V 1 (fun p ↦ (ddWeight p : ℂ) * D [1] p) b :=
    (hD.2 [1] (by simp) 1).mul_smooth hV hμ
  let r := fun p ↦ (ddWeight p : ℂ) * (e p - u p)
  have hr : LocallyIntegrableOn r V :=
    ((hop.2.2.1.mono_set hVU).sub hx.1).continuousOn_mul
      hμ.continuous.continuousOn hV.isLocallyClosed
  have hres := ae_eq_zero_of_forall_test hV ((hr.add ha.2.1).add hb.2.1) (by
    intro η hη
    have hz (p) (hp : p ∉ V) :
        η p = 0 ∧ partialX η p = 0 ∧ partialY η p = 0 :=
      ⟨image_eq_zero_of_notMem_tsupport (fun ht ↦ hp (hη.tsupport_subset ht)),
        image_eq_zero_of_notMem_tsupport (fun ht ↦
          hp (hη.tsupport_subset (tsupport_partialX_subset η ht))),
        image_eq_zero_of_notMem_tsupport (fun ht ↦
          hp (hη.tsupport_subset (tsupport_partialY_subset η ht)))⟩
    have ht := hop.2.2.2 η (hη.mono hVU)
    have hleft : (∫ p in cellSquare, (ddWeight p : ℂ) * (e p - u p) * η p) =
        ∫ p, r p * η p :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun p hp ↦ by simp [(hz p (fun h ↦ hp (hVU h))).1])
    have hright :
        (∫ p in cellSquare, (ddWeight p : ℂ) *
          (ux p * partialX η p + uy p * partialY η p)) =
        ∫ p, (ddWeight p : ℂ) * D [0] p * coordPartial 0 η p +
          (ddWeight p : ℂ) * D [1] p * coordPartial 1 η p := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp ↦ by
        obtain ⟨_, hx0, hy0⟩ := hz p (fun h ↦ hp (hVU h))
        simp [hx0, hy0])]
      apply integral_congr_ae
      filter_upwards [hux, huy] with p hxp hyp
      by_cases hp : p ∈ V
      · simp [hxp hp, hyp hp, coordPartial, mul_add, mul_assoc]
      · obtain ⟨_, hx0, hy0⟩ := hz p hp
        simp [coordPartial, hx0, hy0]
    have i0 := integrable_mul_of_tsupport_subset hr hη.contDiff.continuous
      hη.hasCompactSupport hη.tsupport_subset
    have ia := integrable_mul_of_tsupport_subset ha.2.1 hη.contDiff.continuous
      hη.hasCompactSupport hη.tsupport_subset
    have ib := integrable_mul_of_tsupport_subset hb.2.1 hη.contDiff.continuous
      hη.hasCompactSupport hη.tsupport_subset
    have ix := integrable_mul_of_tsupport_subset ha.1 (hη.continuous_coordPartial 0)
      (hη.hasCompactSupport_coordPartial 0)
      ((tsupport_coordPartial_subset 0 η).trans hη.tsupport_subset)
    have iy := integrable_mul_of_tsupport_subset hb.1 (hη.continuous_coordPartial 1)
      (hη.hasCompactSupport_coordPartial 1)
      ((tsupport_coordPartial_subset 1 η).trans hη.tsupport_subset)
    rw [hleft, hright, integral_add ix iy, ha.2.2 η hη, hb.2.2 η hη] at ht
    simp only [Pi.add_apply, add_mul]
    rw [integral_add (f := fun p ↦ r p * η p + a p * η p) (i0.add ia) ib,
      integral_add i0 ia]
    linear_combination ht)
  filter_upwards [hux, huy, hres] with p hxp hyp hres hp
  refine ⟨hxp hp, hyp hp, ?_⟩
  have hs : 0 < dipoleLift p := by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell (hVU hp)
  have hμ0 : (ddWeight p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero _ hs.ne')
  have hh := hres hp
  dsimp only [Pi.add_apply, r, a, b] at hh
  rw [ddJetOperator, hD.1]
  field_simp
  linear_combination hh


/-- On smooth functions the algebraic weak-jet expression is the classical
    weighted operator, including its totalized values outside the cell. -/
theorem ddOperator_eq_jet {v : ℝ × ℝ → ℂ}
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) :
    ddOperator v = ddJetOperator (fun w ↦ classicalComplexJet w v) := by
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by simp)
  have hx := (contDiff_partialX hv2).differentiable one_ne_zero
  have hy := (contDiff_partialY hv2).differentiable one_ne_zero
  have hμ := contDiff_ddWeight_complex.differentiable (by simp)
  funext p
  simp only [ddOperator, ddWeightedLaplacian, ddJetOperator, classicalComplexJet,
    coordPartial, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
  rw [partialX_mul (hμ p) (hx p), partialY_mul (hμ p) (hy p)]

private theorem green_L2_add {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} {f g : ι → α → ℂ} {F G : α → ℂ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : ∀ n, MemLp (g n) 2 μ)
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ)
    (hflim : Tendsto (fun n ↦ eLpNorm (fun p ↦ f n p - F p) 2 μ) l (𝓝 0))
    (hglim : Tendsto (fun n ↦ eLpNorm (fun p ↦ g n p - G p) 2 μ) l (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun p ↦ (f n p + g n p) - (F p + G p)) 2 μ) l (𝓝 0) := by
  have hft := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf F hF).mpr hflim
  have hgt := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg G hG).mpr hglim
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n p ↦ f n p + g n p) (fun n ↦ (hf n).add (hg n))
    (fun p ↦ F p + G p) (hF.add hG)).mp
  simpa only [MemLp.toLp_add] using! hft.add hgt

private theorem green_L2_sub {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} {f g : ι → α → ℂ} {F G : α → ℂ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : ∀ n, MemLp (g n) 2 μ)
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ)
    (hflim : Tendsto (fun n ↦ eLpNorm (fun p ↦ f n p - F p) 2 μ) l (𝓝 0))
    (hglim : Tendsto (fun n ↦ eLpNorm (fun p ↦ g n p - G p) 2 μ) l (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun p ↦ (f n p - g n p) - (F p - G p)) 2 μ) l (𝓝 0) := by
  have hft := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf F hF).mpr hflim
  have hgt := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg G hG).mpr hglim
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n p ↦ f n p - g n p) (fun n ↦ (hf n).sub (hg n))
    (fun p ↦ F p - G p) (hF.sub hG)).mp
  simpa only [MemLp.toLp_sub] using! hft.sub hgt

private theorem green_L2_mul {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} {c : α → ℂ} (hc : MemLp c ⊤ μ)
    {f : ι → α → ℂ} {F : α → ℂ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hF : MemLp F 2 μ)
    (hflim : Tendsto (fun n ↦ eLpNorm (fun p ↦ f n p - F p) 2 μ) l (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun p ↦ c p * f n p - c p * F p) 2 μ) l (𝓝 0) := by
  let M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
    (ContinuousLinearMap.mul ℂ ℂ).holderL μ ⊤ 2 2 (hc.toLp c)
  have hM {a : α → ℂ} (ha : MemLp a 2 μ) :
      M (ha.toLp a) = (hc.mul ha).toLp (fun p ↦ c p * a p) := by
    apply Lp.ext
    have hm : M (ha.toLp a) =ᵐ[μ] fun p ↦ (hc.toLp c) p * (ha.toLp a) p :=
      (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder _ _
    have hca : MemLp (fun p ↦ c p * a p) 2 μ := hc.mul ha
    filter_upwards [hm, hc.coeFn_toLp, ha.coeFn_toLp, hca.coeFn_toLp]
      with p hp hcp hap hcap
    simp only [hcp, hap] at hp
    exact hp.trans hcap.symm
  have ht := M.continuous.tendsto _ |>.comp
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf F hF).mpr hflim)
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n p ↦ c p * f n p) (fun n ↦ hc.mul (hf n))
    (fun p ↦ c p * F p) (hc.mul hF)).mp
  simpa only [Function.comp_def, hM] using ht

/-- Strong L² convergence of the full classical jet implies convergence of the
    weighted operator on a precompact patch of the positive cell. -/
theorem ddOperator_tendsto_L2_of_jet {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVU : closure V ⊆ cellSquare)
    {v : ℕ → ℝ × ℝ → ℂ}
    (hv : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (v n))
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ w, w.length ≤ 2 → MemLp (D w) 2 (volume.restrict V))
    (hvm : ∀ w, w.length ≤ 2 →
      ∀ n, MemLp (classicalComplexJet w (v n)) 2 (volume.restrict V))
    (hvlim : ∀ w, w.length ≤ 2 →
      Tendsto (fun n ↦ eLpNorm (fun p ↦ classicalComplexJet w (v n) p - D w p)
        2 (volume.restrict V)) atTop (𝓝 0)) :
    (∀ n, MemLp (ddOperator (v n)) 2 (volume.restrict V)) ∧
      MemLp (ddJetOperator D) 2 (volume.restrict V) ∧
      Tendsto (fun n ↦ eLpNorm (fun p ↦ ddOperator (v n) p - ddJetOperator D p)
        2 (volume.restrict V)) atTop (𝓝 0) := by
  let μ := volume.restrict V
  let c := fun p ↦ (ddWeight p : ℂ)
  have hc := contDiff_ddWeight_complex
  have hcx := contDiff_coordPartial_top 0 hc
  have hcy := contDiff_coordPartial_top 1 hc
  have hc0 (p) (hp : p ∈ closure V) : c p ≠ 0 := by
    have hs : 0 < dipoleLift p := by
      simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell (hVU hp)
    exact Complex.ofReal_ne_zero.mpr (pow_ne_zero _ hs.ne')
  have hbound {f : ℝ × ℝ → ℂ} (hf : ContinuousOn f (closure V))
      (hm : AEStronglyMeasurable f μ) : MemLp f ⊤ μ := by
    obtain ⟨C, hC⟩ := hVc.exists_bound_of_continuousOn hf
    exact memLp_top_of_bound hm C
      (ae_restrict_of_forall_mem hV.measurableSet fun p hp ↦ hC p (subset_closure hp))
  have mC : MemLp c ⊤ μ := hbound hc.continuous.continuousOn hc.continuous.aestronglyMeasurable
  have mX : MemLp (coordPartial 0 c) ⊤ μ :=
    hbound hcx.continuous.continuousOn hcx.continuous.aestronglyMeasurable
  have mY : MemLp (coordPartial 1 c) ⊤ μ :=
    hbound hcy.continuous.continuousOn hcy.continuous.aestronglyMeasurable
  have mI : MemLp (fun p ↦ (c p)⁻¹) ⊤ μ :=
    hbound (hc.continuous.continuousOn.inv₀ hc0) hc.continuous.aestronglyMeasurable.inv₀
  let J := fun n w ↦ classicalComplexJet w (v n)
  let T := fun (E : List (Fin 2) → ℝ × ℝ → ℂ) p ↦
    coordPartial 0 c p * E [0] p + c p * E [0, 0] p +
      (coordPartial 1 c p * E [1] p + c p * E [1, 1] p)
  have hmul {a : ℝ × ℝ → ℂ} (ha : MemLp a ⊤ μ) (w) (hw : w.length ≤ 2) :
      (∀ n, MemLp (fun p ↦ a p * J n w p) 2 μ) ∧
        MemLp (fun p ↦ a p * D w p) 2 μ ∧
        Tendsto (fun n ↦ eLpNorm (fun p ↦ a p * J n w p - a p * D w p) 2 μ)
          atTop (𝓝 0) :=
    ⟨fun n ↦ ha.mul (hvm w hw n), ha.mul (hD w hw),
      green_L2_mul ha (hvm w hw) (hD w hw) (hvlim w hw)⟩
  obtain ⟨mx, mxd, tx⟩ := hmul mX [0] (by simp)
  obtain ⟨mxx, mxxd, txx⟩ := hmul mC [0, 0] (by simp)
  obtain ⟨my, myd, ty⟩ := hmul mY [1] (by simp)
  obtain ⟨myy, myyd, tyy⟩ := hmul mC [1, 1] (by simp)
  have mT : ∀ n, MemLp (T (J n)) 2 μ :=
    fun n ↦ ((mx n).add (mxx n)).add ((my n).add (myy n))
  have mTD : MemLp (T D) 2 μ := (mxd.add mxxd).add (myd.add myyd)
  have tT : Tendsto (fun n ↦ eLpNorm (fun p ↦ T (J n) p - T D p) 2 μ) atTop (𝓝 0) :=
    green_L2_add (fun n ↦ (mx n).add (mxx n)) (fun n ↦ (my n).add (myy n))
      (mxd.add mxxd) (myd.add myyd)
      (green_L2_add mx mxx mxd mxxd tx txx) (green_L2_add my myy myd myyd ty tyy)
  have hop (E) : ddJetOperator E = fun p ↦ E [] p - (c p)⁻¹ * T E p := by
    funext p
    simp only [ddJetOperator, T, c, div_eq_mul_inv, mul_comm]
  have hclass (n) := ddOperator_eq_jet (hv n)
  have mOp (n) : MemLp (ddOperator (v n)) 2 μ := by
    rw [hclass, hop]
    exact (hvm [] (by simp) n).sub (mI.mul (mT n))
  refine ⟨mOp, ?_, ?_⟩
  · rw [hop]
    exact (hD [] (by simp)).sub (mI.mul mTD)
  · simp_rw [hclass, hop]
    exact green_L2_sub (hvm [] (by simp)) (fun n ↦ mI.mul (mT n))
      (hD [] (by simp)) (mI.mul mTD) (hvlim [] (by simp))
      (green_L2_mul mI mT mTD tT)

/-- Jet convergence reaches the supplied weak forcing, rather than an
    unidentified second-order expression. -/
theorem HasDDOperator.tendsto_L2_of_jet {u e ux uy : ℝ × ℝ → ℂ}
    (hop : HasDDOperator u e ux uy) {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVU : closure V ⊆ cellSquare)
    {D : List (Fin 2) → ℝ × ℝ → ℂ} (hj : HasWeakJetOn 2 V u D)
    (hD : ∀ w, w.length ≤ 2 → MemLp (D w) 2 (volume.restrict V))
    {v : ℕ → ℝ × ℝ → ℂ}
    (hv : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (v n))
    (hvm : ∀ w, w.length ≤ 2 →
      ∀ n, MemLp (classicalComplexJet w (v n)) 2 (volume.restrict V))
    (hvlim : ∀ w, w.length ≤ 2 →
      Tendsto (fun n ↦ eLpNorm (fun p ↦ classicalComplexJet w (v n) p - D w p)
        2 (volume.restrict V)) atTop (𝓝 0)) :
    (∀ n, MemLp (ddOperator (v n)) 2 (volume.restrict V)) ∧
      MemLp e 2 (volume.restrict V) ∧
      Tendsto (fun n ↦ eLpNorm (fun p ↦ ddOperator (v n) p - e p)
        2 (volume.restrict V)) atTop (𝓝 0) := by
  obtain ⟨hm, hE, ht⟩ := ddOperator_tendsto_L2_of_jet hV hVc hVU hv hD hvm hvlim
  have hae : e =ᵐ[volume.restrict V] ddJetOperator D :=
    (ae_restrict_iff' hV.measurableSet).mpr
      ((hop.ae_eq_jet hV (subset_closure.trans hVU) hj).mono fun p hp hV ↦ (hp hV).2.2)
  refine ⟨hm, hE.ae_eq hae.symm, ?_⟩
  have heq (n) :
      eLpNorm (fun p ↦ ddOperator (v n) p - e p) 2 (volume.restrict V) =
        eLpNorm (fun p ↦ ddOperator (v n) p - ddJetOperator D p) 2 (volume.restrict V) :=
    eLpNorm_congr_ae (hae.mono fun p hp ↦ congrArg (fun z ↦ ddOperator (v n) p - z) hp)
  simpa only [heq] using ht

/-- Local H² smooth approximation can be chosen with classical operator values
    converging to the prescribed weak forcing. Compact support is in the original
    cell, not in the approximation patch. -/
theorem HasDDOperator.local_smooth_approximation {u e ux uy : ℝ × ℝ → ℂ}
    (hop : HasDDOperator u e ux uy) (hu : MemSobolevLocOn 2 cellSquare u)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVU : closure V ⊆ cellSquare) :
    ∃ D : List (Fin 2) → ℝ × ℝ → ℂ,
      HasWeakJetOn 2 V u D ∧
      (∀ w, w.length ≤ 2 → MemLp (D w) 2 (volume.restrict V)) ∧
      ∃ v : ℕ → ℝ × ℝ → ℂ,
        (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (v n) ∧
          HasCompactSupport (v n) ∧ tsupport (v n) ⊆ cellSquare) ∧
        (∀ w, w.length ≤ 2 →
          (∀ n, MemLp (classicalComplexJet w (v n)) 2 (volume.restrict V)) ∧
          Tendsto (fun n ↦ eLpNorm (fun p ↦ classicalComplexJet w (v n) p - D w p)
            2 (volume.restrict V)) atTop (𝓝 0)) ∧
        (∀ n, MemLp (ddOperator (v n)) 2 (volume.restrict V)) ∧
        MemLp e 2 (volume.restrict V) ∧
        Tendsto (fun n ↦ eLpNorm (fun p ↦ ddOperator (v n) p - e p)
          2 (volume.restrict V)) atTop (𝓝 0) := by
  obtain ⟨D, hj, hD, v, hv, hlim⟩ :=
    local_h2_smooth_approximation isOpen_cellSquare hV hVc hVU hu
  exact ⟨D, hj, hD, v, hv, hlim,
    hop.tendsto_L2_of_jet hV hVc hVU hj hD (fun n ↦ (hv n).1)
      (fun w hw ↦ (hlim w hw).1) (fun w hw ↦ (hlim w hw).2)⟩

/-- Scalar coefficient `q(s)` of the weighted virial field. -/
def ddVirialQ (s : ℝ) : ℝ := (s ^ 3 - 8) / (3 * s ^ 2)

def ddVirialField₁ (p : ℝ × ℝ) : ℝ :=
  ddVirialQ (dipoleLift p) * partialX dipoleLift p / gradSq dipoleLift p

def ddVirialField₂ (p : ℝ × ℝ) : ℝ :=
  ddVirialQ (dipoleLift p) * partialY dipoleLift p / gradSq dipoleLift p

/-- Adapted coefficient `f = F/μ`. -/
def ddVirialCoeff (p : ℝ × ℝ) : ℝ := ddF p / ddWeight p

/-- Classical Picone operator `P = -div(M∇) - F`, on the punctured cell. -/
def ddPiconeOperator (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  -(partialX (fun q ↦ (ddMxx q : ℂ) * partialX u q +
      (ddMxy q : ℂ) * partialY u q) p +
    partialY (fun q ↦ (ddMxy q : ℂ) * partialX u q +
      (ddMyy q : ℂ) * partialY u q) p) - (ddF p : ℂ) * u p

/-- Weighted divergence of a smooth real vector field. -/
def ddWeightedDiv (W₁ W₂ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  divergence (fun q ↦ ddWeight q * W₁ q) (fun q ↦ ddWeight q * W₂ q) p / ddWeight p

/-- Weighted half-density generator evaluated on specified first derivatives. -/
def ddWeightedGenerator (W₁ W₂ : ℝ × ℝ → ℝ) (u ux uy : ℝ × ℝ → ℂ)
    (p : ℝ × ℝ) : ℂ :=
  (W₁ p : ℂ) * ux p + (W₂ p : ℂ) * uy p +
    ((ddWeightedDiv W₁ W₂ p / 2 : ℝ) : ℂ) * u p

/-- The cell with the elliptic center removed; all virial coefficients are smooth here. -/
def ddRegularCell : Set (ℝ × ℝ) := {p | p ∈ cellSquare ∧ gradSq dipoleLift p ≠ 0}

theorem ddVirialField₁_eq :
    ddVirialField₁ = fun p ↦ ddVirialQ (dipoleLift p) * -Real.sin p.1 / gradSq dipoleLift p := by
  funext p
  rw [ddVirialField₁, partialX_dipoleLift]

theorem ddVirialField₂_eq :
    ddVirialField₂ = fun p ↦ ddVirialQ (dipoleLift p) * -Real.sin p.2 / gradSq dipoleLift p := by
  funext p
  rw [ddVirialField₂, partialY_dipoleLift]

/-- The radial coefficient has a particularly simple derivative away from zero. -/
theorem hasDerivAt_ddVirialQ {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt ddVirialQ (1 / 3 + 16 / (3 * s ^ 3)) s := by
  have h := (((hasDerivAt_id s).pow 3).sub_const 8).div
    (((hasDerivAt_id s).pow 2).const_mul 3) (by positivity : 3 * s ^ 2 ≠ 0)
  convert h using 1
  · rfl
  · simp only [id_eq, Pi.pow_apply]
    field_simp
    ring

theorem contDiffAt_ddVirialField {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ddVirialField₁ p ∧
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ddVirialField₂ p := by
  have hq : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q ↦ ddVirialQ (dipoleLift q)) p := by
    unfold ddVirialQ
    have hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dipoleLift := by
      unfold dipoleLift
      fun_prop
    exact ((hΨ.contDiffAt.pow 3).sub
      contDiffAt_const).div
      (contDiffAt_const.mul ((by unfold dipoleLift; fun_prop :
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dipoleLift).contDiffAt.pow 2)) (by positivity)
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gradSq dipoleLift) := by
    simp only [gradSq_dipoleLift]
    fun_prop
  constructor
  · unfold ddVirialField₁
    exact (hq.mul (by rw [partialX_dipoleLift]; fun_prop)).div hg.contDiffAt hr
  · unfold ddVirialField₂
    exact (hq.mul (by rw [partialY_dipoleLift]; fun_prop)).div hg.contDiffAt hr

theorem partialX_ddVirialField₁ {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    partialX ddVirialField₁ p =
      (1 / 3 + 16 / (3 * dipoleLift p ^ 3)) * Real.sin p.1 ^ 2 / gradSq dipoleLift p -
      ddVirialQ (dipoleLift p) * Real.cos p.1 / gradSq dipoleLift p +
      2 * ddVirialQ (dipoleLift p) * Real.sin p.1 ^ 2 * Real.cos p.1 /
        gradSq dipoleLift p ^ 2 := by
  have hq := (hasDerivAt_ddVirialQ hs).comp p.1
    ((Real.hasDerivAt_cos p.1).add_const (Real.cos p.2))
  have h : HasDerivAt (fun t ↦ ddVirialQ (Real.cos t + Real.cos p.2) *
      -Real.sin t / (Real.sin t ^ 2 + Real.sin p.2 ^ 2)) _ p.1 :=
    (hq.mul (Real.hasDerivAt_sin p.1).neg).div
    (((Real.hasDerivAt_sin p.1).pow 2).add_const (Real.sin p.2 ^ 2))
      (by simpa only [gradSq_dipoleLift, Pi.pow_apply] using hr)
  rw [ddVirialField₁_eq]
  simp only [partialX, dipoleLift, gradSq_dipoleLift]
  simp only [Pi.mul_apply, Pi.neg_apply, Function.comp_apply, dipoleLift] at h
  rw [h.deriv]
  simp only [gradSq_dipoleLift] at hr
  field_simp
  ring

theorem partialY_ddVirialField₁ {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    partialY ddVirialField₁ p =
      (1 / 3 + 16 / (3 * dipoleLift p ^ 3)) * Real.sin p.1 * Real.sin p.2 /
        gradSq dipoleLift p +
      2 * ddVirialQ (dipoleLift p) * Real.sin p.1 * Real.sin p.2 * Real.cos p.2 /
        gradSq dipoleLift p ^ 2 := by
  have hq := (hasDerivAt_ddVirialQ hs).comp p.2
    ((Real.hasDerivAt_cos p.2).const_add (Real.cos p.1))
  have h : HasDerivAt (fun t ↦ ddVirialQ (Real.cos p.1 + Real.cos t) *
      -Real.sin p.1 / (Real.sin p.1 ^ 2 + Real.sin t ^ 2)) _ p.2 :=
    (hq.mul_const (-Real.sin p.1)).div
    (((Real.hasDerivAt_sin p.2).pow 2).const_add (Real.sin p.1 ^ 2))
      (by simpa only [gradSq_dipoleLift, Pi.pow_apply] using hr)
  rw [ddVirialField₁_eq]
  simp only [partialY, dipoleLift, gradSq_dipoleLift]
  simp only [Function.comp_apply, dipoleLift] at h
  rw [h.deriv]
  simp only [gradSq_dipoleLift] at hr
  field_simp
  ring

theorem partialX_ddVirialField₂ {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    partialX ddVirialField₂ p =
      (1 / 3 + 16 / (3 * dipoleLift p ^ 3)) * Real.sin p.1 * Real.sin p.2 /
        gradSq dipoleLift p +
      2 * ddVirialQ (dipoleLift p) * Real.sin p.1 * Real.sin p.2 * Real.cos p.1 /
        gradSq dipoleLift p ^ 2 := by
  have hq := (hasDerivAt_ddVirialQ hs).comp p.1
    ((Real.hasDerivAt_cos p.1).add_const (Real.cos p.2))
  have h : HasDerivAt (fun t ↦ ddVirialQ (Real.cos t + Real.cos p.2) *
      -Real.sin p.2 / (Real.sin t ^ 2 + Real.sin p.2 ^ 2)) _ p.1 :=
    (hq.mul_const (-Real.sin p.2)).div
    (((Real.hasDerivAt_sin p.1).pow 2).add_const (Real.sin p.2 ^ 2))
      (by simpa only [gradSq_dipoleLift, Pi.pow_apply] using hr)
  rw [ddVirialField₂_eq]
  simp only [partialX, dipoleLift, gradSq_dipoleLift]
  simp only [Function.comp_apply, dipoleLift] at h
  rw [h.deriv]
  simp only [gradSq_dipoleLift] at hr
  field_simp
  ring

theorem partialY_ddVirialField₂ {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    partialY ddVirialField₂ p =
      (1 / 3 + 16 / (3 * dipoleLift p ^ 3)) * Real.sin p.2 ^ 2 / gradSq dipoleLift p -
      ddVirialQ (dipoleLift p) * Real.cos p.2 / gradSq dipoleLift p +
      2 * ddVirialQ (dipoleLift p) * Real.sin p.2 ^ 2 * Real.cos p.2 /
        gradSq dipoleLift p ^ 2 := by
  have hq := (hasDerivAt_ddVirialQ hs).comp p.2
    ((Real.hasDerivAt_cos p.2).const_add (Real.cos p.1))
  have h : HasDerivAt (fun t ↦ ddVirialQ (Real.cos p.1 + Real.cos t) *
      -Real.sin t / (Real.sin p.1 ^ 2 + Real.sin t ^ 2)) _ p.2 :=
    (hq.mul (Real.hasDerivAt_sin p.2).neg).div
    (((Real.hasDerivAt_sin p.2).pow 2).const_add (Real.sin p.1 ^ 2))
      (by simpa only [gradSq_dipoleLift, Pi.pow_apply] using hr)
  rw [ddVirialField₂_eq]
  simp only [partialY, dipoleLift, gradSq_dipoleLift]
  simp only [Pi.mul_apply, Pi.neg_apply, Function.comp_apply, dipoleLift] at h
  rw [h.deriv]
  simp only [gradSq_dipoleLift] at hr
  field_simp
  ring

/-- Conjugating a half-density by Ψ changes its divergence by twice the
    logarithmic derivative of Ψ. No smoothness of the function acted on is used. -/
theorem ddWeightedDiv_eq {W₁ W₂ : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hW₁ : DifferentiableAt ℝ W₁ p) (hW₂ : DifferentiableAt ℝ W₂ p)
    (hs : dipoleLift p ≠ 0) :
    ddWeightedDiv W₁ W₂ p = divergence W₁ W₂ p -
      2 * (Real.sin p.1 * W₁ p + Real.sin p.2 * W₂ p) / dipoleLift p := by
  have hm : DifferentiableAt ℝ ddWeight p := by unfold ddWeight dipoleLift; fun_prop
  have hx : partialX ddWeight p = -2 * dipoleLift p * Real.sin p.1 := by
    exact (((Real.hasDerivAt_cos p.1).add_const (Real.cos p.2)).pow 2).deriv.trans
      (by unfold dipoleLift; ring)
  have hy : partialY ddWeight p = -2 * dipoleLift p * Real.sin p.2 := by
    exact (((Real.hasDerivAt_cos p.2).const_add (Real.cos p.1)).pow 2).deriv.trans
      (by unfold dipoleLift; ring)
  unfold ddWeightedDiv divergence
  rw [show (fun q ↦ ddWeight q * W₁ q) = (fun q ↦ ddWeight q • W₁ q) from rfl,
    show (fun q ↦ ddWeight q * W₂ q) = (fun q ↦ ddWeight q • W₂ q) from rfl,
    partialX_smul hm hW₁, partialY_smul hm hW₂, hx, hy]
  simp only [smul_eq_mul, ddWeight]
  field_simp
  ring

/-- The half-density conjugation only needs the pointwise weak product-rule
    relations, not classical derivatives of either representative. -/
theorem ddWeightedGenerator_conjugation {W₁ W₂ : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hW₁ : DifferentiableAt ℝ W₁ p) (hW₂ : DifferentiableAt ℝ W₂ p)
    (hs : dipoleLift p ≠ 0) {u ux uy v vx vy : ℂ}
    (hv : (dipoleLift p : ℂ) * u = v)
    (hx : -(Real.sin p.1 : ℂ) * u + (dipoleLift p : ℂ) * ux = vx)
    (hy : -(Real.sin p.2 : ℂ) * u + (dipoleLift p : ℂ) * uy = vy) :
    (dipoleLift p : ℂ) *
      ddWeightedGenerator W₁ W₂ (fun _ ↦ u) (fun _ ↦ ux) (fun _ ↦ uy) p =
      (W₁ p : ℂ) * vx + (W₂ p : ℂ) * vy +
        ((divergence W₁ W₂ p / 2 : ℝ) : ℂ) * v := by
  rw [← hv, ← hx, ← hy]
  unfold ddWeightedGenerator
  rw [ddWeightedDiv_eq hW₁ hW₂ hs]
  have hsC : (dipoleLift p : ℂ) ≠ 0 := by exact_mod_cast hs
  push_cast
  field_simp
  ring

/-- A level cutoff adds its normal derivative to weighted divergence. -/
theorem ddWeightedDiv_cutoff {χ : ℝ → ℝ}
    (hχ : Differentiable ℝ χ) {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    ddWeightedDiv (fun q ↦ χ (dipoleLift q) * ddVirialField₁ q)
      (fun q ↦ χ (dipoleLift q) * ddVirialField₂ q) p =
      χ (dipoleLift p) * ddWeightedDiv ddVirialField₁ ddVirialField₂ p +
        deriv χ (dipoleLift p) * ddVirialQ (dipoleLift p) := by
  have hd := contDiffAt_ddVirialField hs hr
  have hW₁ := hd.1.differentiableAt (by simp)
  have hW₂ := hd.2.differentiableAt (by simp)
  have hc : DifferentiableAt ℝ (fun q ↦ χ (dipoleLift q)) p :=
    (hχ _).comp p (by unfold dipoleLift; fun_prop)
  have hcx : partialX (fun q ↦ χ (dipoleLift q)) p =
      deriv χ (dipoleLift p) * -Real.sin p.1 :=
    ((hχ _).hasDerivAt.comp p.1
      ((Real.hasDerivAt_cos p.1).add_const (Real.cos p.2))).deriv
  have hcy : partialY (fun q ↦ χ (dipoleLift q)) p =
      deriv χ (dipoleLift p) * -Real.sin p.2 :=
    ((hχ _).hasDerivAt.comp p.2
      ((Real.hasDerivAt_cos p.2).const_add (Real.cos p.1))).deriv
  rw [ddWeightedDiv_eq
    (W₁ := fun q ↦ χ (dipoleLift q) * ddVirialField₁ q)
    (W₂ := fun q ↦ χ (dipoleLift q) * ddVirialField₂ q)
    (hc.mul hW₁) (hc.mul hW₂) hs, ddWeightedDiv_eq hW₁ hW₂ hs]
  unfold divergence
  rw [show (fun q ↦ χ (dipoleLift q) * ddVirialField₁ q) =
      (fun q ↦ χ (dipoleLift q) • ddVirialField₁ q) from rfl,
    show (fun q ↦ χ (dipoleLift q) * ddVirialField₂ q) =
      (fun q ↦ χ (dipoleLift q) • ddVirialField₂ q) from rfl,
    partialX_smul hc hW₁, partialY_smul hc hW₂, hcx, hcy]
  simp only [smul_eq_mul, ddVirialField₁, ddVirialField₂,
    partialX_dipoleLift, partialY_dipoleLift]
  field_simp [hr]
  rw [gradSq_dipoleLift]
  ring

/-- Cutoff bookkeeping for the weighted half-density generator uses only
    specified first-gradient values, with no classical derivatives of u. -/
theorem ddWeightedGenerator_cutoff {χ : ℝ → ℝ}
    (hχ : Differentiable ℝ χ) (u ux uy : ℝ × ℝ → ℂ)
    {p : ℝ × ℝ} (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    ddWeightedGenerator (fun q ↦ χ (dipoleLift q) * ddVirialField₁ q)
      (fun q ↦ χ (dipoleLift q) * ddVirialField₂ q) u ux uy p =
      (χ (dipoleLift p) : ℂ) *
        ddWeightedGenerator ddVirialField₁ ddVirialField₂ u ux uy p +
      ((deriv χ (dipoleLift p) * ddVirialQ (dipoleLift p) / 2 : ℝ) : ℂ) * u p := by
  unfold ddWeightedGenerator
  rw [ddWeightedDiv_cutoff hχ hs hr]
  push_cast
  ring

/-- Weighted divergence differs from ordinary divergence by 2q(s)/s. -/
theorem ddWeightedDiv_virial {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    ddWeightedDiv ddVirialField₁ ddVirialField₂ p =
      partialX ddVirialField₁ p + partialY ddVirialField₂ p +
        2 * ddVirialQ (dipoleLift p) / dipoleLift p := by
  have hd := contDiffAt_ddVirialField hs hr
  rw [ddWeightedDiv_eq (hd.1.differentiableAt (by simp))
    (hd.2.differentiableAt (by simp)) hs]
  simp only [divergence, ddVirialField₁, ddVirialField₂,
    partialX_dipoleLift, partialY_dipoleLift]
  field_simp
  rw [gradSq_dipoleLift] at *
  ring

/-- Pointwise differential algebra; only the two explicit denominators need be nonzero. -/
theorem dd_virial_algebra_at {p : ℝ × ℝ}
    (hs : dipoleLift p ≠ 0) (hr : gradSq dipoleLift p ≠ 0) :
    (classicalL0 ddVirialField₁ p - Real.cos p.2 * ddVirialField₂ p =
      ddVirialCoeff p * Real.sin p.2 ∧
      classicalL0 ddVirialField₂ p + Real.cos p.1 * ddVirialField₁ p =
        -(ddVirialCoeff p * Real.sin p.1)) ∧
    ddVirialCoeff p - ddWeightedDiv ddVirialField₁ ddVirialField₂ p = -1 ∧
    ddWeight p * (2 * partialX ddVirialField₁ p - ddVirialCoeff p) = ddMxx p ∧
    ddWeight p * (partialY ddVirialField₁ p + partialX ddVirialField₂ p) = ddMxy p ∧
    ddWeight p * (2 * partialY ddVirialField₂ p - ddVirialCoeff p) = ddMyy p := by
  have hx : Real.sin p.1 ^ 2 = 1 - Real.cos p.1 ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq p.1]
  have hy : Real.sin p.2 ^ 2 = 1 - Real.cos p.2 ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq p.2]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [classicalL0, smul_eq_mul, ddWeightedDiv_virial hs hr,
      partialX_ddVirialField₁ hs hr, partialY_ddVirialField₁ hs hr,
      partialX_ddVirialField₂ hs hr, partialY_ddVirialField₂ hs hr]
    simp only [ddVirialField₁, ddVirialField₂, partialX_dipoleLift, partialY_dipoleLift,
      ddVirialCoeff, ddWeight, ddF, ddMxx, ddMxy, ddMyy, ddA, ddC, ddVirialQ]
    simp only [gradSq_dipoleLift, dipoleLift] at hs hr ⊢
    field_simp
    simp only [hx, hy]
    ring

/-- Adaptedness, constant weighted defect, and all three entries of
    `μ(2 sym DW - f I) = M`. -/
theorem dd_virial_algebra :
    IsAdaptedOn ddVirialField₁ ddVirialField₂ ddVirialCoeff ddRegularCell ∧
      ∀ p ∈ ddRegularCell,
        ddVirialCoeff p - ddWeightedDiv ddVirialField₁ ddVirialField₂ p = -1 ∧
        ddWeight p * (2 * partialX ddVirialField₁ p - ddVirialCoeff p) = ddMxx p ∧
        ddWeight p * (partialY ddVirialField₁ p + partialX ddVirialField₂ p) = ddMxy p ∧
        ddWeight p * (2 * partialY ddVirialField₂ p - ddVirialCoeff p) = ddMyy p := by
  have hlocal (p) (hp : p ∈ ddRegularCell) := dd_virial_algebra_at
    (show dipoleLift p ≠ 0 from ne_of_gt (by
      simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp.1)) hp.2
  exact ⟨fun p hp ↦ (hlocal p hp).1, fun p hp ↦ (hlocal p hp).2⟩

/-- Function-level virial density, with the value of `Eu` supplied separately. -/
def ddVirialDensity (u e ux uy : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ddF p * (‖e p‖ ^ 2 - ‖u p‖ ^ 2) + ddMatrixForm p (ux p) (uy p)

/-- The weighted virial's inward derivative `∇u · ∇Ψ/|∇Ψ|`. The shared
    `normalDeriv` has the opposite, outward orientation. -/
def ddInwardNormal (ux uy : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  -normalDeriv ux uy p

/-- The boundary term in flow time. The last term includes `dℓ = √r dt`.
    No pointwise gradient trace on every level is claimed. -/
def ddVirialLevel (u e ux uy : ℝ × ℝ → ℂ) (ε : ℝ) : ℝ :=
  levelIntegral (ε / 2) (fun p ↦
    (8 - ε ^ 3) / 3 * (‖ddInwardNormal ux uy p‖ ^ 2 - ‖tangentDeriv ux uy p‖ ^ 2 -
      ‖u p‖ ^ 2 + (e p * (starRingEnd ℂ) (u p)).re) -
    ε ^ 2 * gradNorm p * ((starRingEnd ℂ) (u p) * ddInwardNormal ux uy p).re)

/-- Planar boundary density whose restriction to Ψ = ε is the level integrand. -/
def ddBoundaryDensity (u e ux uy : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  (8 - dipoleLift p ^ 3) / 3 *
    (‖ddInwardNormal ux uy p‖ ^ 2 - ‖tangentDeriv ux uy p‖ ^ 2 -
      ‖u p‖ ^ 2 + (e p * (starRingEnd ℂ) (u p)).re) -
    dipoleLift p ^ 2 * gradNorm p *
      ((starRingEnd ℂ) (u p) * ddInwardNormal ux uy p).re

/-- The boundary density identifies the level term without choosing gradient traces
    or splitting possibly nonintegrable level integrals. -/
theorem levelIntegral_ddBoundaryDensity (u e ux uy : ℝ × ℝ → ℂ)
    {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    levelIntegral h (ddBoundaryDensity u e ux uy) = ddVirialLevel u e ux uy (2 * h) := by
  unfold ddVirialLevel
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  unfold levelIntegral
  apply intervalIntegral.integral_congr
  intro t _
  simp only [ddBoundaryDensity, dipoleLift_dipoleOrbit h0 h1]

/-- First component of the Green flux evaluated on a specified weak gradient. -/
def ddWeakGreenFlux₁ (u ux uy : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ddWeight p * (-((starRingEnd ℂ) (u p) * ux p).re -
    2 * (((ddVirialField₁ p : ℂ) * ux p +
      (ddVirialField₂ p : ℂ) * uy p) * (starRingEnd ℂ) (ux p)).re +
    ddVirialField₁ p * (‖ux p‖ ^ 2 + ‖uy p‖ ^ 2 + ‖u p‖ ^ 2))

/-- Second component of the Green flux evaluated on a specified weak gradient. -/
def ddWeakGreenFlux₂ (u ux uy : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ddWeight p * (-((starRingEnd ℂ) (u p) * uy p).re -
    2 * (((ddVirialField₁ p : ℂ) * ux p +
      (ddVirialField₂ p : ℂ) * uy p) * (starRingEnd ℂ) (uy p)).re +
    ddVirialField₂ p * (‖ux p‖ ^ 2 + ‖uy p‖ ^ 2 + ‖u p‖ ^ 2))

/-- Contraction of the weak Green flux with ∇Ψ, in flow-time normalization. -/
def ddGreenNormalFlux (u ux uy : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  partialX dipoleLift p * ddWeakGreenFlux₁ u ux uy p +
    partialY dipoleLift p * ddWeakGreenFlux₂ u ux uy p

/-- Boundary-flux algebra for arbitrary values and a specified gradient on the
    regular cell; it needs no differential equation or regularity of those values. -/
theorem dd_boundary_flux (u e ux uy : ℝ × ℝ → ℂ) {p : ℝ × ℝ}
    (hp : p ∈ ddRegularCell) :
    ddGreenNormalFlux u ux uy p - ddWeight p * ddVirialQ (dipoleLift p) *
      (e p * (starRingEnd ℂ) (u p)).re = ddBoundaryDensity u e ux uy p := by
  have hs : dipoleLift p ≠ 0 := ne_of_gt (by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp.1)
  have hρ2 : gradNorm p ^ 2 = gradSq dipoleLift p := by
    rw [gradNorm, gradSq_dipoleLift, Real.sq_sqrt (by positivity)]
  have hρ : gradNorm p ≠ 0 := by
    intro hz
    apply hp.2
    rw [← hρ2, hz]
    norm_num
  have hframe := norm_normalDeriv_sq_add_norm_tangentDeriv_sq ux uy hρ
  have hT : ‖tangentDeriv ux uy p‖ ^ 2 =
      ‖ux p‖ ^ 2 + ‖uy p‖ ^ 2 - ‖normalDeriv ux uy p‖ ^ 2 := by linarith
  have hcoeff : (8 - dipoleLift p ^ 3) / 3 =
      -(ddWeight p * ddVirialQ (dipoleLift p)) := by
    unfold ddWeight ddVirialQ
    field_simp
    ring
  rw [ddBoundaryDensity, ddInwardNormal, norm_neg, hT, hcoeff]
  simp only [ddGreenNormalFlux, ddWeakGreenFlux₁, ddWeakGreenFlux₂,
    ddVirialField₁, ddVirialField₂, partialX_dipoleLift, partialY_dipoleLift,
    normalDeriv, norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hρ2,
    Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im,
    Complex.div_ofReal_re, Complex.div_ofReal_im]
  dsimp only [ddWeight]
  field_simp [hp.2]
  rw [gradSq_dipoleLift]
  ring

/-- First component of the classical Green flux. -/
def ddGreenFlux₁ (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ddWeight p * (-((starRingEnd ℂ) (u p) * partialX u p).re -
    2 * (((ddVirialField₁ p : ℂ) * partialX u p +
      (ddVirialField₂ p : ℂ) * partialY u p) * (starRingEnd ℂ) (partialX u p)).re +
    ddVirialField₁ p * (‖partialX u p‖ ^ 2 + ‖partialY u p‖ ^ 2 + ‖u p‖ ^ 2))

/-- Second component of the classical Green flux. -/
def ddGreenFlux₂ (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  ddWeight p * (-((starRingEnd ℂ) (u p) * partialY u p).re -
    2 * (((ddVirialField₁ p : ℂ) * partialX u p +
      (ddVirialField₂ p : ℂ) * partialY u p) * (starRingEnd ℂ) (partialY u p)).re +
    ddVirialField₂ p * (‖partialX u p‖ ^ 2 + ‖partialY u p‖ ^ 2 + ‖u p‖ ^ 2))

/-- Derivative of the quadratic Green flux along a real parameter. -/
private theorem hasDerivAt_greenFlux
    {m a b c : ℝ → ℝ} {v x y z : ℝ → ℂ}
    {m' a' b' c' : ℝ} {v' x' y' z' : ℂ} {t : ℝ}
    (hm : HasDerivAt m m' t) (ha : HasDerivAt a a' t)
    (hb : HasDerivAt b b' t) (hc : HasDerivAt c c' t)
    (hv : HasDerivAt v v' t) (hx : HasDerivAt x x' t)
    (hy : HasDerivAt y y' t) (hz : HasDerivAt z z' t) :
    HasDerivAt
      (fun s ↦ m s * (-((starRingEnd ℂ) (v s) * z s).re -
        2 * (((a s : ℂ) * x s + (b s : ℂ) * y s) *
          (starRingEnd ℂ) (z s)).re +
        c s * (‖x s‖ ^ 2 + ‖y s‖ ^ 2 + ‖v s‖ ^ 2)))
      (m' * (-((starRingEnd ℂ) (v t) * z t).re -
        2 * (((a t : ℂ) * x t + (b t : ℂ) * y t) *
          (starRingEnd ℂ) (z t)).re +
        c t * (‖x t‖ ^ 2 + ‖y t‖ ^ 2 + ‖v t‖ ^ 2)) +
       m t * (-((starRingEnd ℂ) v' * z t + (starRingEnd ℂ) (v t) * z').re -
        2 * ((((a' : ℂ) * x t + (a t : ℂ) * x' +
          ((b' : ℂ) * y t + (b t : ℂ) * y')) * (starRingEnd ℂ) (z t) +
          ((a t : ℂ) * x t + (b t : ℂ) * y t) * (starRingEnd ℂ) z').re) +
        (c' * (‖x t‖ ^ 2 + ‖y t‖ ^ 2 + ‖v t‖ ^ 2) +
          c t * (2 * (x' * (starRingEnd ℂ) (x t)).re +
            2 * (y' * (starRingEnd ℂ) (y t)).re +
            2 * (v' * (starRingEnd ℂ) (v t)).re)))) t := by
  have hreal {f : ℝ → ℂ} {d : ℂ} (h : HasDerivAt f d t) :
      HasDerivAt (fun s ↦ (f s).re) d.re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  convert hm.mul (((hreal (hv.star.mul hz)).neg.sub
    ((hreal (((ha.ofReal_comp.mul hx).add (hb.ofReal_comp.mul hy)).mul hz.star)).const_mul 2)).add
    (hc.mul ((hx.norm_sq.add hy.norm_sq).add hv.norm_sq))) using 1 <;>
    simp only [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply,
      Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply] <;> rfl

/-- Normal/tangential and Cartesian expressions for the same quadratic form. -/
theorem ddMatrixForm_eq_cartesian (vx vy : ℂ) {p : ℝ × ℝ}
    (hr : gradSq dipoleLift p ≠ 0) :
    ddMatrixForm p vx vy =
      ddMxx p * ‖vx‖ ^ 2 + 2 * ddMxy p * (vx * (starRingEnd ℂ) vy).re +
        ddMyy p * ‖vy‖ ^ 2 := by
  have hρ2 : gradNorm p ^ 2 = gradSq dipoleLift p := by
    rw [gradNorm, gradSq_dipoleLift, Real.sq_sqrt (by positivity)]
  simp only [ddMatrixForm, normalDeriv, tangentDeriv, norm_div, div_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, hρ2,
    ddMxx, ddMxy, ddMyy, Complex.sq_norm, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  field_simp
  rw [gradSq_dipoleLift]
  ring

/-- Local classical Green identity, separate from its weak annular justification. -/
theorem dd_green {u : ℝ × ℝ → ℂ} (hu : ContDiffOn ℝ 3 u ddRegularCell)
    {p : ℝ × ℝ} (hp : p ∈ ddRegularCell) :
    ddWeight p * ddVirialCoeff p *
        (‖ddOperator u p‖ ^ 2 - (ddOperator u p * (starRingEnd ℂ) (u p)).re) +
      2 * ddWeight p * (ddWeightedGenerator ddVirialField₁ ddVirialField₂
        u (partialX u) (partialY u) p * (starRingEnd ℂ) (ddOperator u p)).re =
      ddVirialDensity u (ddOperator u) (partialX u) (partialY u) p +
        divergence (ddGreenFlux₁ u) (ddGreenFlux₂ u) p := by
  have hU : IsOpen ddRegularCell :=
    isOpen_cellSquare.inter (isOpen_ne.preimage (by
      simp only [gradSq_dipoleLift]
      fun_prop))
  have hat : ContDiffAt ℝ 3 u p := hu.contDiffAt (hU.mem_nhds hp)
  have hud : DifferentiableAt ℝ u p := hat.differentiableAt (by norm_num)
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) p :=
    (hat.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hex : partialX u =ᶠ[𝓝 p] fun q ↦ fderiv ℝ u q (1, 0) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact partialX_eq_fderiv ((hu.contDiffAt (hU.mem_nhds hq)).differentiableAt (by norm_num))
  have hey : partialY u =ᶠ[𝓝 p] fun q ↦ fderiv ℝ u q (0, 1) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact partialY_eq_fderiv ((hu.contDiffAt (hU.mem_nhds hq)).differentiableAt (by norm_num))
  have hux : DifferentiableAt ℝ (partialX u) p :=
    (hfd.clm_apply (differentiableAt_const _)).congr_of_eventuallyEq hex
  have huy : DifferentiableAt ℝ (partialY u) p :=
    (hfd.clm_apply (differentiableAt_const _)).congr_of_eventuallyEq hey
  have hmix : partialY (partialX u) p = partialX (partialY u) p := by
    have hxd := (hfd.clm_apply (differentiableAt_const (1, 0)))
    have hyd := (hfd.clm_apply (differentiableAt_const (0, 1)))
    have hxx : partialY (partialX u) p =
        partialY (fun q ↦ fderiv ℝ u q (1, 0)) p :=
      (hasDerivAt_partialY hxd).congr_of_eventuallyEq
        (hex.comp_tendsto ((continuous_const.prodMk continuous_id).tendsto p.2)) |>.deriv
    have hyy : partialX (partialY u) p =
        partialX (fun q ↦ fderiv ℝ u q (0, 1)) p :=
      (hasDerivAt_partialX hyd).congr_of_eventuallyEq
        (hey.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto p.1)) |>.deriv
    rw [hxx, hyy, partialY_eq_fderiv hxd, partialX_eq_fderiv hyd,
      fderiv_clm_apply hfd (differentiableAt_const _),
      fderiv_clm_apply hfd (differentiableAt_const _)]
    simpa using (hat.isSymmSndFDerivAt (by norm_num)) (0, 1) (1, 0)
  have hs : dipoleLift p ≠ 0 := ne_of_gt (by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp.1)
  have hm : DifferentiableAt ℝ ddWeight p := by unfold ddWeight dipoleLift; fun_prop
  have hw := contDiffAt_ddVirialField hs hp.2
  have hw₁ := hw.1.differentiableAt (by simp)
  have hw₂ := hw.2.differentiableAt (by simp)
  have hx := (hasDerivAt_greenFlux
    (hasDerivAt_partialX hm) (hasDerivAt_partialX hw₁)
    (hasDerivAt_partialX hw₂) (hasDerivAt_partialX hw₁)
    (hasDerivAt_partialX hud) (hasDerivAt_partialX hux)
    (hasDerivAt_partialX huy) (hasDerivAt_partialX hux)).deriv
  have hy := (hasDerivAt_greenFlux
    (hasDerivAt_partialY hm) (hasDerivAt_partialY hw₁)
    (hasDerivAt_partialY hw₂) (hasDerivAt_partialY hw₂)
    (hasDerivAt_partialY hud) (hasDerivAt_partialY hux)
    (hasDerivAt_partialY huy) (hasDerivAt_partialY huy)).deriv
  change partialX (ddGreenFlux₁ u) p = _ at hx
  change partialY (ddGreenFlux₂ u) p = _ at hy
  have hm0 : ddWeight p ≠ 0 := pow_ne_zero _ hs
  have hmx : partialX ddWeight p = 2 * dipoleLift p * partialX dipoleLift p := by
    simpa [ddWeight, partialX, Pi.pow_apply] using!
      ((hasDerivAt_partialX (show DifferentiableAt ℝ dipoleLift p by
        unfold dipoleLift; fun_prop)).pow 2).deriv
  have hmy : partialY ddWeight p = 2 * dipoleLift p * partialY dipoleLift p := by
    simpa [ddWeight, partialY, Pi.pow_apply] using!
      ((hasDerivAt_partialY (show DifferentiableAt ℝ dipoleLift p by
        unfold dipoleLift; fun_prop)).pow 2).deriv
  obtain ⟨hdefect, hxx, hxy, hyy⟩ := (dd_virial_algebra.2 p hp)
  have hF : ddF p = ddWeight p * ddVirialCoeff p := by
    exact (mul_div_cancel₀ (ddF p) hm0).symm
  have hdiv :
      ddWeight p * ddVirialCoeff p -
        ddWeight p * (partialX ddVirialField₁ p + partialY ddVirialField₂ p) -
        partialX ddWeight p * ddVirialField₁ p -
        partialY ddWeight p * ddVirialField₂ p = -ddWeight p := by
    rw [ddWeightedDiv_eq hw₁ hw₂ hs] at hdefect
    rw [hmx, hmy]
    dsimp only [ddWeight]
    simp only [divergence, partialX_dipoleLift, partialY_dipoleLift] at hdefect ⊢
    field_simp at hdefect ⊢
    linear_combination hdefect
  have hop : ddOperator u p = u p -
      (((partialX ddWeight p : ℝ) : ℂ) * partialX u p +
        (ddWeight p : ℂ) * partialX (partialX u) p +
        (((partialY ddWeight p : ℝ) : ℂ) * partialY u p +
          (ddWeight p : ℂ) * partialY (partialY u) p)) / (ddWeight p : ℂ) := by
    unfold ddOperator ddWeightedLaplacian
    have hmc : DifferentiableAt ℝ (fun q ↦ (ddWeight q : ℂ)) p := by
      unfold ddWeight dipoleLift
      fun_prop
    rw [partialX_mul hmc hux, partialY_mul hmc huy]
    have hmx' := (hasDerivAt_partialX hm).ofReal_comp.deriv
    have hmy' := (hasDerivAt_partialY hm).ofReal_comp.deriv
    change partialX (fun q ↦ (ddWeight q : ℂ)) p = _ at hmx'
    change partialY (fun q ↦ (ddWeight q : ℂ)) p = _ at hmy'
    rw [hmx', hmy']
  rw [divergence, hx, hy]
  rw [ddVirialDensity, ddMatrixForm_eq_cartesian _ _ hp.2, hF, ← hxx, ← hxy, ← hyy,
    ddWeightedGenerator, hop, hmix]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    Complex.div_ofReal_re, Complex.div_ofReal_im, zero_mul, add_zero, sub_zero]
  rw [show ddWeightedDiv ddVirialField₁ ddVirialField₂ p = ddVirialCoeff p + 1 by
    linarith [hdefect]]
  field_simp
  linear_combination hdiv * ddWeight p *
    ((u p).re ^ 2 + (u p).im ^ 2 +
      (partialX u p).re ^ 2 + (partialX u p).im ^ 2 +
      (partialY u p).re ^ 2 + (partialY u p).im ^ 2)

/-! ### Smooth cutoff integration of the weighted Green identity -/

section SmoothGreen

open scoped ContDiff

/-- Annular multiplication removes both singular levels of a coefficient. -/
private theorem contDiff_annular_mul {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ Ioo (0 : ℝ) 2) {F : ℝ × ℝ → ℝ} {n : ℕ}
    (hF : ∀ p, 0 < dipoleLift p → dipoleLift p < 2 → ContDiffAt ℝ n F p) :
    ContDiff ℝ n (fun p ↦ χ (dipoleLift p) * F p) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : dipoleLift p ∈ tsupport χ
  · have hs := hχs hp
    exact ((hχ.of_le (by simp)).comp (by unfold dipoleLift; fun_prop)).contDiffAt.mul
      (hF p hs.1 hs.2)
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hz := (notMem_tsupport_iff_eventuallyEq.mp hp).comp_tendsto
      (show Continuous dipoleLift by unfold dipoleLift; fun_prop).continuousAt
    filter_upwards [hz] with q hq
    change χ (dipoleLift q) = 0 at hq
    simp [hq]

/-- The classical operator is local even on totalized representatives. -/
private theorem ddOperator_eq_zero_of_notMem_tsupport (u : ℝ × ℝ → ℂ)
    {p : ℝ × ℝ} (hp : p ∉ tsupport u) : ddOperator u p = 0 := by
  have hv : u p = 0 := image_eq_zero_of_notMem_tsupport hp
  have hx : ∀ᶠ q in 𝓝 p, partialX u q = 0 := by
    filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hp] with q hq
    exact image_eq_zero_of_notMem_tsupport (fun h ↦ hq (tsupport_partialX_subset u h))
  have hy : ∀ᶠ q in 𝓝 p, partialY u q = 0 := by
    filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hp] with q hq
    exact image_eq_zero_of_notMem_tsupport (fun h ↦ hq (tsupport_partialY_subset u h))
  have hmx : ∀ᶠ q in 𝓝 p, (ddWeight q : ℂ) * partialX u q = 0 := by
    filter_upwards [hx] with q hq; simp [hq]
  have hmy : ∀ᶠ q in 𝓝 p, (ddWeight q : ℂ) * partialY u q = 0 := by
    filter_upwards [hy] with q hq; simp [hq]
  simp [ddOperator, ddWeightedLaplacian, hv,
    partialX_eq_zero_of_eventually hmx, partialY_eq_zero_of_eventually hmy]

/-- Cutoff-generator bookkeeping also holds at the totalized singular points:
    the cutoff field vanishes on a neighbourhood of every such point. -/
private theorem ddWeightedGenerator_cutoff_global {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo (0 : ℝ) 2)
    (u ux uy : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    ddWeightedGenerator (fun q ↦ χ (dipoleLift q) * ddVirialField₁ q)
      (fun q ↦ χ (dipoleLift q) * ddVirialField₂ q) u ux uy p =
      (χ (dipoleLift p) : ℂ) *
        ddWeightedGenerator ddVirialField₁ ddVirialField₂ u ux uy p +
      ((deriv χ (dipoleLift p) * ddVirialQ (dipoleLift p) / 2 : ℝ) : ℂ) * u p := by
  by_cases hp : dipoleLift p ∈ tsupport χ
  · have hs := hχs hp
    exact ddWeightedGenerator_cutoff (hχ.differentiable (by simp)) u ux uy
      hs.1.ne' (gradSq_dipoleLift_pos hs.1 hs.2).ne'
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hp
    have hc : χ (dipoleLift p) = 0 := hz.self_of_nhds
    have hd : deriv χ (dipoleLift p) = 0 := by
      rw [hz.deriv_eq]
      exact deriv_const _ _
    have hzc := hz.comp_tendsto
      (show Continuous dipoleLift by unfold dipoleLift; fun_prop).continuousAt
    have h₁ : ∀ᶠ q in 𝓝 p,
        ddWeight q * (χ (dipoleLift q) * ddVirialField₁ q) = 0 := by
      filter_upwards [hzc] with q hq
      change χ (dipoleLift q) = 0 at hq
      simp [hq]
    have h₂ : ∀ᶠ q in 𝓝 p,
        ddWeight q * (χ (dipoleLift q) * ddVirialField₂ q) = 0 := by
      filter_upwards [hzc] with q hq
      change χ (dipoleLift q) = 0 at hq
      simp [hq]
    simp [ddWeightedGenerator, ddWeightedDiv, divergence, hc, hd,
      partialX_eq_zero_of_eventually h₁, partialY_eq_zero_of_eventually h₂]

private theorem integral_divergence_eq_zero_real {F₁ F₂ : ℝ × ℝ → ℝ}
    (h₁ : ContDiff ℝ 1 F₁) (h₂ : ContDiff ℝ 1 F₂)
    (hc₁ : HasCompactSupport F₁) (hc₂ : HasCompactSupport F₂) :
    Integrable (divergence F₁ F₂) ∧ ∫ p, divergence F₁ F₂ p = 0 := by
  have hx : Integrable (partialX F₁) :=
    (contDiff_partialX (n := 0) (by simpa using h₁)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.intro hc₁ fun p hp ↦
        partialX_eq_zero_of_eventually (notMem_tsupport_iff_eventuallyEq.mp hp))
  have hy : Integrable (partialY F₂) :=
    (contDiff_partialY (n := 0) (by simpa using h₂)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.intro hc₂ fun p hp ↦
        partialY_eq_zero_of_eventually (notMem_tsupport_iff_eventuallyEq.mp hp))
  have ex := integral_partialX_eq_zero (Complex.ofRealCLM.contDiff.comp h₁)
    (hc₁.comp_left Complex.ofReal_zero)
  have ey := integral_partialY_eq_zero (Complex.ofRealCLM.contDiff.comp h₂)
    (hc₂.comp_left Complex.ofReal_zero)
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at ex ey
  rw [partialX_ofReal (h₁.differentiable one_ne_zero)] at ex
  rw [partialY_ofReal (h₂.differentiable one_ne_zero)] at ey
  have exr : (∫ p, partialX F₁ p) = 0 := by
    simpa only [integral_complex_ofReal, Complex.ofReal_eq_zero] using! ex
  have eyr : (∫ p, partialY F₂ p) = 0 := by
    simpa only [integral_complex_ofReal, Complex.ofReal_eq_zero] using! ey
  refine ⟨hx.add hy, ?_⟩
  change (∫ p, partialX F₁ p + partialY F₂ p) = 0
  rw [integral_add hx hy]
  rw [exr, eyr, add_zero]

private theorem green_contDiffAt_re {f : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ 1 f p) : ContDiffAt ℝ 1 (fun q ↦ (f q).re) p :=
  Complex.reCLM.contDiff.contDiffAt.comp p hf

private theorem green_contDiffAt_im {f : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ 1 f p) : ContDiffAt ℝ 1 (fun q ↦ (f q).im) p :=
  Complex.imCLM.contDiff.contDiffAt.comp p hf

private theorem green_contDiffAt_ofReal {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ 1 f p) : ContDiffAt ℝ 1 (fun q ↦ (f q : ℂ)) p := by
  simpa only [Complex.ofRealCLM_apply] using! Complex.ofRealCLM.contDiff.contDiffAt.comp p hf

private theorem green_contDiffAt_norm_sq {f : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (hf : ContDiffAt ℝ 1 f p) : ContDiffAt ℝ 1 (fun q ↦ ‖f q‖ ^ 2) p :=
  hf.norm_sq ℂ

attribute [local fun_prop] green_contDiffAt_re green_contDiffAt_im
  green_contDiffAt_ofReal green_contDiffAt_norm_sq

/-- The classical Green identity integrated against an annular cutoff.
    This is the smooth endpoint for local H² approximation; compact support is
    in the original cell, not in the annulus where approximation is performed. -/
theorem dd_smooth_green {u : ℝ × ℝ → ℂ} (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport u) (hus : tsupport u ⊆ cellSquare)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ Ioo (0 : ℝ) 2) :
    (∫ p in cellSquare, χ (dipoleLift p) *
      ddVirialDensity u (ddOperator u) (partialX u) (partialY u) p) =
      (∫ p in cellSquare, ddWeight p * χ (dipoleLift p) * ddVirialCoeff p *
        (‖ddOperator u p‖ ^ 2 - (ddOperator u p * (starRingEnd ℂ) (u p)).re)) +
      2 * (∫ p in cellSquare, ddWeight p *
        (ddWeightedGenerator (fun q ↦ χ (dipoleLift q) * ddVirialField₁ q)
          (fun q ↦ χ (dipoleLift q) * ddVirialField₂ q)
          u (partialX u) (partialY u) p *
          (starRingEnd ℂ) (ddOperator u p)).re) +
      ∫ p in cellSquare, deriv χ (dipoleLift p) *
        (ddGreenNormalFlux u (partialX u) (partialY u) p -
          ddWeight p * ddVirialQ (dipoleLift p) *
            (ddOperator u p * (starRingEnd ℂ) (u p)).re) := by
  let e := ddOperator u
  let G : ℝ × ℝ → ℂ := fun p ↦
    (ddVirialField₁ p : ℂ) * partialX u p + (ddVirialField₂ p : ℂ) * partialY u p +
      ((ddVirialCoeff p + 1 : ℝ) : ℂ) / 2 * u p
  let A : ℝ × ℝ → ℝ := fun p ↦ ddWeight p * ddVirialCoeff p *
    (‖e p‖ ^ 2 - (e p * (starRingEnd ℂ) (u p)).re)
  let B : ℝ × ℝ → ℝ := fun p ↦ ddWeight p * (G p * (starRingEnd ℂ) (e p)).re
  let Q : ℝ × ℝ → ℝ := fun p ↦ ddWeight p * ddVirialQ (dipoleLift p) *
    (e p * (starRingEnd ℂ) (u p)).re
  let N := ddGreenNormalFlux u (partialX u) (partialY u)
  let V₁ : ℝ × ℝ → ℝ := fun p ↦ χ (dipoleLift p) * ddGreenFlux₁ u p
  let V₂ : ℝ × ℝ → ℝ := fun p ↦ χ (dipoleLift p) * ddGreenFlux₂ u p
  have hux : ContDiff ℝ 2 (partialX u) := contDiff_partialX (hu.of_le (by simp))
  have huy : ContDiff ℝ 2 (partialY u) := contDiff_partialY (hu.of_le (by simp))
  have hm : ContDiff ℝ 2 ddWeight := by unfold ddWeight dipoleLift; fun_prop
  have hn : ContDiff ℝ 1 (fun p ↦
      partialX (fun q ↦ (ddWeight q : ℂ) * partialX u q) p +
      partialY (fun q ↦ (ddWeight q : ℂ) * partialY u q) p) :=
    (contDiff_partialX ((Complex.ofRealCLM.contDiff.comp hm).mul hux)).add
      (contDiff_partialY ((Complex.ofRealCLM.contDiff.comp hm).mul huy))
  have he (p) (hs : 0 < dipoleLift p) : ContDiffAt ℝ 1 e p := by
    have hμc : ContDiff ℝ 1 (fun q ↦ (ddWeight q : ℂ)) := by
      simpa only [Function.comp_def, Complex.ofRealCLM_apply] using!
        Complex.ofRealCLM.contDiff.comp (hm.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
    have hv : ContDiffAt ℝ 1 u p := (hu.of_le (by simp)).contDiffAt
    have hdiv : ContDiffAt ℝ 1 (fun q ↦
        (partialX (fun r ↦ (ddWeight r : ℂ) * partialX u r) q +
          partialY (fun r ↦ (ddWeight r : ℂ) * partialY u r) q) /
            (ddWeight q : ℂ)) p :=
      by
        simpa only [div_eq_mul_inv] using!
          hn.contDiffAt.mul (hμc.contDiffAt.inv
            (Complex.ofReal_ne_zero.mpr (pow_ne_zero _ hs.ne')))
    exact hv.sub hdiv
  have hcoeff (p) (hs : 0 < dipoleLift p) (ht : dipoleLift p < 2) :
      ContDiffAt ℝ 1 ddVirialField₁ p ∧ ContDiffAt ℝ 1 ddVirialField₂ p ∧
        ContDiffAt ℝ 1 ddVirialCoeff p ∧
        ContDiffAt ℝ 1 (fun q ↦ ddVirialQ (dipoleLift q)) p := by
    have hr := (gradSq_dipoleLift_pos hs ht).ne'
    have hw := contDiffAt_ddVirialField hs.ne' hr
    refine ⟨hw.1.of_le (by simp), hw.2.of_le (by simp), ?_, ?_⟩
    · have hd : ContDiffAt ℝ 1 dipoleLift p := by unfold dipoleLift; fun_prop
      have hg : ContDiffAt ℝ 1 (gradSq dipoleLift) p := by
        simp only [gradSq_dipoleLift]
        fun_prop
      unfold ddVirialCoeff ddF ddWeight
      fun_prop (disch := positivity)
    · unfold ddVirialQ
      have hd : ContDiffAt ℝ 1 dipoleLift p := by unfold dipoleLift; fun_prop
      exact ((hd.pow 3).sub contDiffAt_const).div
        (contDiffAt_const.mul (hd.pow 2)) (by positivity)
  have hflux (p) (hs : 0 < dipoleLift p) (ht : dipoleLift p < 2) :
      ContDiffAt ℝ 1 (ddGreenFlux₁ u) p ∧ ContDiffAt ℝ 1 (ddGreenFlux₂ u) p := by
    obtain ⟨hw₁, hw₂, hf, hq⟩ := hcoeff p hs ht
    have hx := (hux.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt (x := p)
    have hy := (huy.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt (x := p)
    have hv := (hu.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).contDiffAt (x := p)
    have hμ := (hm.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt (x := p)
    constructor
    · unfold ddGreenFlux₁
      fun_prop
    · unfold ddGreenFlux₂
      fun_prop
  have hV₁ : ContDiff ℝ 1 V₁ :=
    contDiff_annular_mul hχ hχs fun p hs ht ↦ (hflux p hs ht).1
  have hV₂ : ContDiff ℝ 1 V₂ :=
    contDiff_annular_mul hχ hχs fun p hs ht ↦ (hflux p hs ht).2
  have hzero (p) (hp : p ∉ tsupport u) :
      u p = 0 ∧ partialX u p = 0 ∧ partialY u p = 0 ∧ e p = 0 :=
    ⟨image_eq_zero_of_notMem_tsupport hp,
      image_eq_zero_of_notMem_tsupport (fun h ↦ hp (tsupport_partialX_subset u h)),
      image_eq_zero_of_notMem_tsupport (fun h ↦ hp (tsupport_partialY_subset u h)),
      ddOperator_eq_zero_of_notMem_tsupport u hp⟩
  have hzflux (p) (hp : p ∉ tsupport u) :
      ddGreenFlux₁ u p = 0 ∧ ddGreenFlux₂ u p = 0 := by
    obtain ⟨hv, hx, hy, _⟩ := hzero p hp
    simp [ddGreenFlux₁, ddGreenFlux₂, hv, hx, hy]
  have hcV₁ : HasCompactSupport V₁ := HasCompactSupport.intro hc fun p hp ↦ by
    simp [V₁, (hzflux p hp).1]
  have hcV₂ : HasCompactSupport V₂ := HasCompactSupport.intro hc fun p hp ↦ by
    simp [V₂, (hzflux p hp).2]
  obtain ⟨iDiv, hDiv⟩ := integral_divergence_eq_zero_real hV₁ hV₂ hcV₁ hcV₂
  have hDivZero (p) (hp : p ∉ tsupport u) : divergence V₁ V₂ p = 0 := by
    have hz₁ : ∀ᶠ q in 𝓝 p, V₁ q = 0 := by
      filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hp] with q hq
      simp [V₁, (hzflux q hq).1]
    have hz₂ : ∀ᶠ q in 𝓝 p, V₂ q = 0 := by
      filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hp] with q hq
      simp [V₂, (hzflux q hq).2]
    simp [divergence, partialX_eq_zero_of_eventually hz₁, partialY_eq_zero_of_eventually hz₂]
  have hDivCell : (∫ p in cellSquare, divergence V₁ V₂ p) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun p hp ↦ hDivZero p (fun h ↦ hp (hus h)))]
    exact hDiv
  have hreg (p) (hs : 0 < dipoleLift p) (ht : dipoleLift p < 2) :
      ContDiffAt ℝ 1 A p ∧ ContDiffAt ℝ 1 B p ∧
        ContDiffAt ℝ 1 Q p ∧ ContDiffAt ℝ 1 N p := by
    obtain ⟨hw₁, hw₂, hf, hq⟩ := hcoeff p hs ht
    have hv := (hu.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).contDiffAt (x := p)
    have hx := (hux.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt (x := p)
    have hy := (huy.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt (x := p)
    have hμ := (hm.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt (x := p)
    have he' := he p hs
    have hg : ContDiffAt ℝ 1 G p := by dsimp only [G]; fun_prop
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [A]; fun_prop
    · dsimp only [B]; fun_prop
    · dsimp only [Q]; fun_prop
    · obtain ⟨hf₁, hf₂⟩ := hflux p hs ht
      change ContDiffAt ℝ 1 (fun q ↦ partialX dipoleLift q * ddGreenFlux₁ u q +
        partialY dipoleLift q * ddGreenFlux₂ u q) p
      simp only [partialX_dipoleLift, partialY_dipoleLift]
      fun_prop
  have hzreg (p) (hp : p ∉ tsupport u) : A p = 0 ∧ B p = 0 ∧ Q p = 0 ∧ N p = 0 := by
    obtain ⟨hv, hx, hy, he'⟩ := hzero p hp
    simp [A, B, Q, N, G, ddGreenNormalFlux, ddWeakGreenFlux₁, ddWeakGreenFlux₂, hv, hx, hy, he']
  have hint {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (hηs : tsupport η ⊆ Ioo (0 : ℝ) 2)
      {F : ℝ × ℝ → ℝ}
      (hF : ∀ p, 0 < dipoleLift p → dipoleLift p < 2 → ContDiffAt ℝ 1 F p)
      (hF0 : ∀ p ∉ tsupport u, F p = 0) :
      Integrable (fun p ↦ η (dipoleLift p) * F p) :=
    (contDiff_annular_mul hη hηs hF).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.intro hc fun p hp ↦ by rw [hF0 p hp, mul_zero])
  have hχ' : ContDiff ℝ ∞ (deriv χ) := hχ.deriv'
  have hχ's : tsupport (deriv χ) ⊆ Ioo (0 : ℝ) 2 := tsupport_deriv_subset.trans hχs
  have iA := (hint hχ hχs (fun p hs ht ↦ (hreg p hs ht).1)
    (fun p hp ↦ (hzreg p hp).1)).integrableOn (s := cellSquare)
  have iB := (hint hχ hχs (fun p hs ht ↦ (hreg p hs ht).2.1)
    (fun p hp ↦ (hzreg p hp).2.1)).integrableOn (s := cellSquare)
  have iQ := (hint hχ' hχ's (fun p hs ht ↦ (hreg p hs ht).2.2.1)
    (fun p hp ↦ (hzreg p hp).2.2.1)).integrableOn (s := cellSquare)
  have iN := (hint hχ' hχ's (fun p hs ht ↦ (hreg p hs ht).2.2.2)
    (fun p hp ↦ (hzreg p hp).2.2.2)).integrableOn (s := cellSquare)
  have hG (p) (hs : 0 < dipoleLift p) (ht : dipoleLift p < 2) :
      ddWeightedGenerator ddVirialField₁ ddVirialField₂ u (partialX u) (partialY u) p = G p := by
    have hd := (dd_virial_algebra_at hs.ne' (gradSq_dipoleLift_pos hs ht).ne').2.1
    have hd' : ddWeightedDiv ddVirialField₁ ddVirialField₂ p = ddVirialCoeff p + 1 := by
      linarith
    simp only [ddWeightedGenerator, G, hd', Complex.ofReal_div, Complex.ofReal_ofNat]
  have hproduct (p) (hs : 0 < dipoleLift p) (ht : dipoleLift p < 2) :
      divergence V₁ V₂ p =
        χ (dipoleLift p) * divergence (ddGreenFlux₁ u) (ddGreenFlux₂ u) p +
          deriv χ (dipoleLift p) * N p := by
    obtain ⟨hf₁, hf₂⟩ := hflux p hs ht
    have hd₁ := hf₁.differentiableAt one_ne_zero
    have hd₂ := hf₂.differentiableAt one_ne_zero
    have hdχ := hχ.differentiable (by simp)
    have hd : DifferentiableAt ℝ (fun q ↦ χ (dipoleLift q)) p :=
      (hdχ _).comp p (by unfold dipoleLift; fun_prop)
    have hx : partialX (fun q ↦ χ (dipoleLift q)) p =
        deriv χ (dipoleLift p) * -Real.sin p.1 :=
      ((hdχ _).hasDerivAt.comp p.1
        ((Real.hasDerivAt_cos p.1).add_const (Real.cos p.2))).deriv
    have hy : partialY (fun q ↦ χ (dipoleLift q)) p =
        deriv χ (dipoleLift p) * -Real.sin p.2 :=
      ((hdχ _).hasDerivAt.comp p.2
        ((Real.hasDerivAt_cos p.2).const_add (Real.cos p.1))).deriv
    change partialX (fun q ↦ χ (dipoleLift q) • ddGreenFlux₁ u q) p +
      partialY (fun q ↦ χ (dipoleLift q) • ddGreenFlux₂ u q) p = _
    rw [partialX_smul hd hd₁, partialY_smul hd hd₂, hx, hy]
    change _ = χ (dipoleLift p) *
      (partialX (ddGreenFlux₁ u) p + partialY (ddGreenFlux₂ u) p) +
        deriv χ (dipoleLift p) *
          (partialX dipoleLift p * ddGreenFlux₁ u p + partialY dipoleLift p * ddGreenFlux₂ u p)
    simp only [smul_eq_mul, partialX_dipoleLift, partialY_dipoleLift]
    ring
  have hpoint (p) (hp : p ∈ cellSquare) :
      χ (dipoleLift p) * ddVirialDensity u e (partialX u) (partialY u) p =
        χ (dipoleLift p) * A p + 2 * (χ (dipoleLift p) * B p) +
          deriv χ (dipoleLift p) * N p - divergence V₁ V₂ p := by
    by_cases hps : dipoleLift p ∈ tsupport χ
    · obtain ⟨hs, ht⟩ := hχs hps
      have hh := dd_green ((hu.of_le (by simp : (3 : WithTop ℕ∞) ≤ ∞)).contDiffOn)
        (show p ∈ ddRegularCell from ⟨hp, (gradSq_dipoleLift_pos hs ht).ne'⟩)
      rw [hG p hs ht] at hh
      dsimp only [A, B, e]
      linear_combination -χ (dipoleLift p) * hh + hproduct p hs ht
    · have hz := notMem_tsupport_iff_eventuallyEq.mp hps
      have hc0 : χ (dipoleLift p) = 0 := hz.self_of_nhds
      have hd0 : deriv χ (dipoleLift p) = 0 := by
        rw [hz.deriv_eq]
        exact deriv_const _ _
      have hz' := hz.comp_tendsto
        (show Continuous dipoleLift by unfold dipoleLift; fun_prop).continuousAt
      have hv₁ : ∀ᶠ q in 𝓝 p, V₁ q = 0 := by
        filter_upwards [hz'] with q hq
        change χ (dipoleLift q) = 0 at hq
        simp [V₁, hq]
      have hv₂ : ∀ᶠ q in 𝓝 p, V₂ q = 0 := by
        filter_upwards [hz'] with q hq
        change χ (dipoleLift q) = 0 at hq
        simp [V₂, hq]
      simp [hc0, hd0, divergence,
        partialX_eq_zero_of_eventually hv₁, partialY_eq_zero_of_eventually hv₂]
  have hmain :
      (∫ p in cellSquare, χ (dipoleLift p) *
        ddVirialDensity u e (partialX u) (partialY u) p) =
      (∫ p in cellSquare, χ (dipoleLift p) * A p) +
        2 * (∫ p in cellSquare, χ (dipoleLift p) * B p) +
        ∫ p in cellSquare, deriv χ (dipoleLift p) * N p := by
    calc
      _ = ∫ p in cellSquare, (χ (dipoleLift p) * A p +
          2 * (χ (dipoleLift p) * B p) + deriv χ (dipoleLift p) * N p) -
            divergence V₁ V₂ p :=
        setIntegral_congr_fun isOpen_cellSquare.measurableSet hpoint
      _ = _ := by
        rw [integral_sub
          (f := fun p ↦ χ (dipoleLift p) * A p +
            2 * (χ (dipoleLift p) * B p) + deriv χ (dipoleLift p) * N p)
          ((iA.add (iB.const_mul 2)).add iN) iDiv.integrableOn,
          integral_add (f := fun p ↦ χ (dipoleLift p) * A p +
            2 * (χ (dipoleLift p) * B p)) (iA.add (iB.const_mul 2)) iN,
          integral_add iA (iB.const_mul 2), integral_const_mul, hDivCell, sub_zero]
  have hcut (p) :
      ddWeight p *
        (ddWeightedGenerator (fun q ↦ χ (dipoleLift q) * ddVirialField₁ q)
          (fun q ↦ χ (dipoleLift q) * ddVirialField₂ q)
          u (partialX u) (partialY u) p * (starRingEnd ℂ) (e p)).re =
      χ (dipoleLift p) * B p + deriv χ (dipoleLift p) * Q p / 2 := by
    rw [ddWeightedGenerator_cutoff_global hχ hχs]
    by_cases hp : dipoleLift p ∈ tsupport χ
    · obtain ⟨hs, ht⟩ := hχs hp
      rw [hG p hs ht]
      simp only [B, Q, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, sub_zero]
      ring
    · have hc0 := image_eq_zero_of_notMem_tsupport hp
      have hd0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hp (tsupport_deriv_subset h))
      simp [hc0, hd0, B, Q]
  have hAint :
      (∫ p in cellSquare, ddWeight p * χ (dipoleLift p) * ddVirialCoeff p *
        (‖e p‖ ^ 2 - (e p * (starRingEnd ℂ) (u p)).re)) =
        ∫ p in cellSquare, χ (dipoleLift p) * A p := by
    apply integral_congr_ae
    exact Eventually.of_forall fun p ↦ by dsimp only [A]; ring
  have hBint :
      (∫ p in cellSquare, ddWeight p *
        (ddWeightedGenerator (fun q ↦ χ (dipoleLift q) * ddVirialField₁ q)
          (fun q ↦ χ (dipoleLift q) * ddVirialField₂ q)
          u (partialX u) (partialY u) p * (starRingEnd ℂ) (e p)).re) =
      (∫ p in cellSquare, χ (dipoleLift p) * B p) +
        (∫ p in cellSquare, deriv χ (dipoleLift p) * Q p) / 2 := by
    calc
      _ = ∫ p in cellSquare, χ (dipoleLift p) * B p +
          deriv χ (dipoleLift p) * Q p / 2 :=
        integral_congr_ae (Eventually.of_forall hcut)
      _ = _ := by rw [integral_add iB (iQ.div_const 2), integral_div]
  have hCint :
      (∫ p in cellSquare, deriv χ (dipoleLift p) * (N p - Q p)) =
      (∫ p in cellSquare, deriv χ (dipoleLift p) * N p) -
        ∫ p in cellSquare, deriv χ (dipoleLift p) * Q p := by
    simp_rw [mul_sub]
    exact integral_sub iN iQ
  change (∫ p in cellSquare, χ (dipoleLift p) *
      ddVirialDensity u e (partialX u) (partialY u) p) =
    (∫ p in cellSquare, ddWeight p * χ (dipoleLift p) * ddVirialCoeff p *
      (‖e p‖ ^ 2 - (e p * (starRingEnd ℂ) (u p)).re)) +
      2 * (∫ p in cellSquare, ddWeight p *
        (ddWeightedGenerator (fun q ↦ χ (dipoleLift q) * ddVirialField₁ q)
          (fun q ↦ χ (dipoleLift q) * ddVirialField₂ q)
          u (partialX u) (partialY u) p * (starRingEnd ℂ) (e p)).re) +
      ∫ p in cellSquare, deriv χ (dipoleLift p) * (N p - Q p)
  rw [hAint, hBint, hCint]
  linear_combination hmain

end SmoothGreen

/-! ### Quadratic stability on the cutoff patch -/

/-- A real quadratic expression in four complex values, written as a finite sum
    of real parts of complex pairings. -/
private def greenQuadratic (a : Fin 4 → Fin 4 → ℝ)
    (z : Fin 4 → ℂ) : ℝ :=
  ∑ i, ∑ j, a i j * (z i * (starRingEnd ℂ) (z j)).re

private theorem green_pair_limit {μ : Measure (ℝ × ℝ)}
    {a : ℝ × ℝ → ℝ} (ha : MemLp a ⊤ μ)
    {f g : ℕ → ℝ × ℝ → ℂ} {F G : ℝ × ℝ → ℂ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : ∀ n, MemLp (g n) 2 μ)
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ)
    (tf : Tendsto (fun n ↦ eLpNorm (fun p ↦ f n p - F p) 2 μ) atTop (𝓝 0))
    (tg : Tendsto (fun n ↦ eLpNorm (fun p ↦ g n p - G p) 2 μ) atTop (𝓝 0)) :
    (∀ n, Integrable (fun p ↦ a p * (f n p * (starRingEnd ℂ) (g n p)).re) μ) ∧
    Integrable (fun p ↦ a p * (F p * (starRingEnd ℂ) (G p)).re) μ ∧
    Tendsto (fun n ↦ ∫ p, a p * (f n p * (starRingEnd ℂ) (g n p)).re ∂μ)
      atTop (𝓝 (∫ p, a p * (F p * (starRingEnd ℂ) (G p)).re ∂μ)) := by
  have hac : MemLp (fun p ↦ (a p : ℂ)) ⊤ μ := ha.ofReal
  have hi {v w : ℝ × ℝ → ℂ} (hv : MemLp v 2 μ) (hw : MemLp w 2 μ) :
      Integrable (fun p ↦ (a p : ℂ) * v p * (starRingEnd ℂ) (w p)) μ := by
    have hav : MemLp (fun p ↦ (a p : ℂ) * v p) 2 μ := hac.mul hv
    exact hav.integrable_mul hw.star
  have heq (v w : ℝ × ℝ → ℂ) :
      (fun p ↦ a p * (v p * (starRingEnd ℂ) (w p)).re) =
      (fun p ↦ ((a p : ℂ) * v p * (starRingEnd ℂ) (w p)).re) := by
    funext p
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hir {v w : ℝ × ℝ → ℂ} (hv : MemLp v 2 μ) (hw : MemLp w 2 μ) :
      Integrable (fun p ↦ a p * (v p * (starRingEnd ℂ) (w p)).re) μ := by
    rw [heq]
    exact Complex.reCLM.integrable_comp (hi hv hw)
  refine ⟨fun n ↦ hir (hf n) (hg n), hir hF hG, ?_⟩
  have h := Complex.continuous_re.tendsto _ |>.comp
    (tendsto_integral_mul_conj_of_L2 hac hf hg hF hG tf tg)
  have hInt {v w : ℝ × ℝ → ℂ} (hv : MemLp v 2 μ) (hw : MemLp w 2 μ) :
      (∫ p, a p * (v p * (starRingEnd ℂ) (w p)).re ∂μ) =
        (∫ p, (a p : ℂ) * v p * (starRingEnd ℂ) (w p) ∂μ).re := by
    rw [heq]
    exact integral_re (hi hv hw)
  simpa only [hInt (hf _) (hg _), hInt hF hG, Function.comp_def] using h

private theorem green_quadratic_limit {μ : Measure (ℝ × ℝ)}
    {a : ℝ × ℝ → Fin 4 → Fin 4 → ℝ}
    (ha : ∀ i j, MemLp (fun p ↦ a p i j) ⊤ μ)
    {z : ℕ → ℝ × ℝ → Fin 4 → ℂ} {Z : ℝ × ℝ → Fin 4 → ℂ}
    (hz : ∀ i n, MemLp (fun p ↦ z n p i) 2 μ)
    (hZ : ∀ i, MemLp (fun p ↦ Z p i) 2 μ)
    (tz : ∀ i, Tendsto (fun n ↦ eLpNorm (fun p ↦ z n p i - Z p i) 2 μ)
      atTop (𝓝 0)) :
    (∀ n, Integrable (fun p ↦ greenQuadratic (a p) (z n p)) μ) ∧
    Integrable (fun p ↦ greenQuadratic (a p) (Z p)) μ ∧
    Tendsto (fun n ↦ ∫ p, greenQuadratic (a p) (z n p) ∂μ) atTop
      (𝓝 (∫ p, greenQuadratic (a p) (Z p) ∂μ)) := by
  have hpair (i j) := green_pair_limit (ha i j) (hz i) (hz j) (hZ i) (hZ j) (tz i) (tz j)
  have hi (n) : Integrable (fun p ↦ greenQuadratic (a p) (z n p)) μ :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ (hpair i j).1 n
  have hI : Integrable (fun p ↦ greenQuadratic (a p) (Z p)) μ :=
    integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ (hpair i j).2.1
  have heq (n) : (∫ p, greenQuadratic (a p) (z n p) ∂μ) =
      ∑ i, ∑ j, ∫ p, a p i j * (z n p i * (starRingEnd ℂ) (z n p j)).re ∂μ := by
    simp only [greenQuadratic]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ fun j _ ↦ (hpair i j).1 n
    · intro i _
      exact integrable_finsetSum _ fun j _ ↦ (hpair i j).1 n
  have hEq : (∫ p, greenQuadratic (a p) (Z p) ∂μ) =
      ∑ i, ∑ j, ∫ p, a p i j * (Z p i * (starRingEnd ℂ) (Z p j)).re ∂μ := by
    simp only [greenQuadratic]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ fun j _ ↦ (hpair i j).2.1
    · intro i _
      exact integrable_finsetSum _ fun j _ ↦ (hpair i j).2.1
  refine ⟨hi, hI, ?_⟩
  simp_rw [heq, hEq]
  exact tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦ (hpair i j).2.2

private theorem green_cutoff_patch {χ : ℝ → ℝ} (hc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (0 : ℝ) 2) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ IsCompact (closure V) ∧
      closure V ⊆ ddRegularCell ∧
      ∀ p ∈ cellSquare, dipoleLift p ∈ tsupport χ → p ∈ V := by
  let K : Set (ℝ × ℝ) := {p | |(diagCoord p).1| ≤ Real.pi / 2 ∧
    |(diagCoord p).2| ≤ Real.pi / 2 ∧ dipoleLift p ∈ tsupport χ}
  have hd₁ : Continuous (fun p : ℝ × ℝ ↦ |(diagCoord p).1|) := by
    unfold diagCoord; fun_prop
  have hd₂ : Continuous (fun p : ℝ × ℝ ↦ |(diagCoord p).2|) := by
    unfold diagCoord; fun_prop
  have hs : Continuous dipoleLift := by unfold dipoleLift; fun_prop
  have hKc : IsClosed K := (isClosed_le hd₁ continuous_const).inter
    ((isClosed_le hd₂ continuous_const).inter (hc.isClosed.preimage hs))
  have hK : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hKc (show
      K ⊆ Icc (-Real.pi) Real.pi ×ˢ Icc (-Real.pi) Real.pi from by
      intro p hp
      obtain ⟨h₁l, h₁u⟩ := abs_le.mp hp.1
      obtain ⟨h₂l, h₂u⟩ := abs_le.mp hp.2.1
      have hx : p.1 = (diagCoord p).1 + (diagCoord p).2 := by dsimp [diagCoord]; ring
      have hy : p.2 = (diagCoord p).1 - (diagCoord p).2 := by dsimp [diagCoord]; ring
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩)
  have hKU : K ⊆ ddRegularCell := by
    intro p hp
    obtain ⟨h0, h2⟩ := hχs hp.2.2
    have hcos : Real.cos (diagCoord p).1 * Real.cos (diagCoord p).2 ≠ 0 := by
      rw [dipoleLift_eq_diag] at h0
      intro hz
      nlinarith [hz]
    have hstrict (t : ℝ) (ht : |t| ≤ Real.pi / 2) (hn : Real.cos t ≠ 0) :
        |t| < Real.pi / 2 := by
      by_contra h
      have he : |t| = Real.pi / 2 := le_antisymm ht (le_of_not_gt h)
      apply hn
      rw [← Real.cos_abs, he, Real.cos_pi_div_two]
    exact ⟨⟨hstrict _ hp.1 (mul_ne_zero_iff.mp hcos).1,
      hstrict _ hp.2.1 (mul_ne_zero_iff.mp hcos).2⟩, (gradSq_dipoleLift_pos h0 h2).ne'⟩
  have hU : IsOpen ddRegularCell :=
    isOpen_cellSquare.inter (isOpen_ne.preimage (by simp only [gradSq_dipoleLift]; fun_prop))
  obtain ⟨V, hV, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  exact ⟨V, hV, hVc, hVU, fun p hp hs ↦ hKV ⟨hp.1.le, hp.2.le, hs⟩⟩

/-- Coefficient tables for the density, forcing bulk term, generator pairing,
    and normal-flux correction. Variables are ordered as (u, e, ux, uy).
    Symmetry of the coefficient tables is not required. -/
private def greenCoefficients (χ : ℝ → ℝ) (p : ℝ × ℝ) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  let s := dipoleLift p
  let x := partialX dipoleLift p
  let y := partialY dipoleLift p
  let w := ddVirialField₁ p
  let v := ddVirialField₂ p
  let r := x * w + y * v
  ![
    ![![-χ s * ddF p, 0, 0, 0], ![0, χ s * ddF p, 0, 0],
      ![0, 0, χ s * ddMxx p, 2 * χ s * ddMxy p], ![0, 0, 0, χ s * ddMyy p]],
    ![![0, 0, 0, 0], ![-ddWeight p * χ s * ddVirialCoeff p,
      ddWeight p * χ s * ddVirialCoeff p, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
    ![![0, ddWeight p * (χ s * (ddVirialCoeff p + 1) + deriv χ s * ddVirialQ s) / 2, 0, 0],
      ![0, 0, 0, 0], ![0, ddWeight p * χ s * w, 0, 0],
      ![0, ddWeight p * χ s * v, 0, 0]],
    ![![deriv χ s * ddWeight p * r, 0, -deriv χ s * ddWeight p * x,
        -deriv χ s * ddWeight p * y],
      ![-deriv χ s * ddWeight p * ddVirialQ s, 0, 0, 0],
      ![0, 0, deriv χ s * ddWeight p * (r - 2 * x * w),
        -2 * deriv χ s * ddWeight p * (x * v + y * w)],
      ![0, 0, 0, deriv χ s * ddWeight p * (r - 2 * y * v)]]
  ]

/-- The four integrands of the cutoff Green identity, in the same order as
    the coefficient tables. -/
private def greenIntegrands (χ : ℝ → ℝ) (u e ux uy : ℝ × ℝ → ℂ)
    (p : ℝ × ℝ) : Fin 4 → ℝ :=
  ![χ (dipoleLift p) * ddVirialDensity u e ux uy p,
    ddWeight p * χ (dipoleLift p) * ddVirialCoeff p *
      (‖e p‖ ^ 2 - (e p * (starRingEnd ℂ) (u p)).re),
    ddWeight p *
      (ddWeightedGenerator (fun q ↦ χ (dipoleLift q) * ddVirialField₁ q)
        (fun q ↦ χ (dipoleLift q) * ddVirialField₂ q) u ux uy p *
        (starRingEnd ℂ) (e p)).re,
    deriv χ (dipoleLift p) * (ddGreenNormalFlux u ux uy p -
      ddWeight p * ddVirialQ (dipoleLift p) * (e p * (starRingEnd ℂ) (u p)).re)]

private theorem green_integrands_quadratic {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (u e ux uy : ℝ × ℝ → ℂ) {p : ℝ × ℝ} (hp : p ∈ ddRegularCell) (k : Fin 4) :
    greenIntegrands χ u e ux uy p k =
      greenQuadratic (greenCoefficients χ p k) ![u p, e p, ux p, uy p] := by
  have hs : dipoleLift p ≠ 0 := ne_of_gt (by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp.1)
  have hd : ddWeightedDiv ddVirialField₁ ddVirialField₂ p = ddVirialCoeff p + 1 := by
    linarith [(dd_virial_algebra_at hs hp.2).2.1]
  have hdχ := ddWeightedDiv_cutoff (hχ.differentiable (by simp)) hs hp.2
  fin_cases k
  · simp [greenIntegrands, greenQuadratic, greenCoefficients, Fin.sum_univ_succ,
      ddVirialDensity, ddMatrixForm_eq_cartesian _ _ hp.2]
    simp only [Complex.sq_norm, Complex.normSq_apply]
    ring
  · simp [greenIntegrands, greenQuadratic, greenCoefficients, Fin.sum_univ_succ]
    simp only [Complex.sq_norm, Complex.normSq_apply]
    ring
  · simp [greenIntegrands, greenQuadratic, greenCoefficients, Fin.sum_univ_succ,
      ddWeightedGenerator, hdχ, hd]
    ring
  · simp [greenIntegrands, greenQuadratic, greenCoefficients, Fin.sum_univ_succ,
      ddGreenNormalFlux, ddWeakGreenFlux₁, ddWeakGreenFlux₂]
    simp only [Complex.sq_norm, Complex.normSq_apply]
    ring

private theorem green_coefficients_continuous {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (k i j : Fin 4) :
    ContinuousOn (fun p ↦ greenCoefficients χ p k i j) ddRegularCell := by
  intro p hp
  have hs : dipoleLift p ≠ 0 := ne_of_gt (by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp.1)
  have hr := hp.2
  have hsC : ContinuousAt dipoleLift p := by unfold dipoleLift; fun_prop
  have hrC : ContinuousAt (gradSq dipoleLift) p := by simp only [gradSq_dipoleLift]; fun_prop
  have hsin₁ : ContinuousAt (fun q : ℝ × ℝ ↦ Real.sin q.1) p :=
    Real.continuous_sin.continuousAt.comp continuousAt_fst
  have hsin₂ : ContinuousAt (fun q : ℝ × ℝ ↦ Real.sin q.2) p :=
    Real.continuous_sin.continuousAt.comp continuousAt_snd
  have hμ : ContinuousAt ddWeight p := by unfold ddWeight dipoleLift; fun_prop
  have hF : ContinuousAt ddF p := by
    unfold ddF
    fun_prop (disch := simp [hr])
  have hA : ContinuousAt ddA p := by
    unfold ddA ddC
    fun_prop (disch := simp [hs, hr])
  have hC : ContinuousAt ddC p := by
    unfold ddC
    fun_prop (disch := simp [hr])
  have hMxx : ContinuousAt ddMxx p := by
    unfold ddMxx
    fun_prop (disch := simp [hr])
  have hMxy : ContinuousAt ddMxy p := by
    unfold ddMxy
    fun_prop (disch := simp [hr])
  have hMyy : ContinuousAt ddMyy p := by
    unfold ddMyy
    fun_prop (disch := simp [hr])
  have hf : ContinuousAt ddVirialCoeff p := by
    unfold ddVirialCoeff
    fun_prop (disch := simp [ddWeight, hs])
  have hq : ContinuousAt (fun q ↦ ddVirialQ (dipoleLift q)) p := by
    unfold ddVirialQ
    fun_prop (disch := simp [hs])
  have hw := (contDiffAt_ddVirialField hs hr).1.continuousAt
  have hv := (contDiffAt_ddVirialField hs hr).2.continuousAt
  have hx : ContinuousAt (partialX dipoleLift) p := by simp only [partialX_dipoleLift]; fun_prop
  have hy : ContinuousAt (partialY dipoleLift) p := by simp only [partialY_dipoleLift]; fun_prop
  have hχc := hχ.continuous
  have hχd := hχ.continuous_deriv (by simp)
  apply ContinuousAt.continuousWithinAt
  dsimp only [greenCoefficients]
  fun_prop

private theorem green_integrands_zero {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχs : tsupport χ ⊆ Ioo (0 : ℝ) 2)
    (u e ux uy : ℝ × ℝ → ℂ) {p : ℝ × ℝ} (hp : dipoleLift p ∉ tsupport χ) (k : Fin 4) :
    greenIntegrands χ u e ux uy p k = 0 := by
  have h0 := image_eq_zero_of_notMem_tsupport hp
  have h1 := image_eq_zero_of_notMem_tsupport (fun h ↦ hp (tsupport_deriv_subset h))
  fin_cases k <;>
    simp [greenIntegrands, ddWeightedGenerator_cutoff_global hχ hχs, h0, h1]

private theorem green_integral_localize {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχs : tsupport χ ⊆ Ioo (0 : ℝ) 2)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V) (hVU : V ⊆ ddRegularCell)
    (hsupp : ∀ p ∈ cellSquare, dipoleLift p ∈ tsupport χ → p ∈ V)
    (u e ux uy : ℝ × ℝ → ℂ) (k : Fin 4) :
    (∫ p in cellSquare, greenIntegrands χ u e ux uy p k) =
      ∫ p in V, greenQuadratic (greenCoefficients χ p k) ![u p, e p, ux p, uy p] := by
  calc
    _ = ∫ p in V, greenIntegrands χ u e ux uy p k :=
      (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero isOpen_cellSquare.measurableSet
        (fun p hp ↦ (hVU hp).1) (fun p hp ↦ green_integrands_zero hχ hχs u e ux uy
          (fun hs ↦ hp.2 (hsupp p hp.1 hs)) k))
    _ = _ := setIntegral_congr_fun hV.measurableSet
      (fun p hp ↦ green_integrands_quadratic hχ u e ux uy (hVU hp) k)

/-- The weighted Green identity tested against an annular level cutoff.
    All derivatives of u are weak witnesses; e realizes Eu weakly. The cutoff
    generator includes its half-density correction. Local H² and L² suffice,
    without an eigenfunction hypothesis or differentiation of e. -/
theorem dd_weak_green {u e ux uy : ℝ × ℝ → ℂ}
    (hu : MemSobolevLocOn 2 cellSquare u) (he : MemSobolevLocOn 0 cellSquare e)
    (hop : HasDDOperator u e ux uy)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ioo (0 : ℝ) 2) :
    (∫ p in cellSquare, χ (dipoleLift p) * ddVirialDensity u e ux uy p) =
      (∫ p in cellSquare, ddWeight p * χ (dipoleLift p) * ddVirialCoeff p *
        (‖e p‖ ^ 2 - (e p * (starRingEnd ℂ) (u p)).re)) +
      2 * (∫ p in cellSquare, ddWeight p *
        (ddWeightedGenerator (fun q ↦ χ (dipoleLift q) * ddVirialField₁ q)
          (fun q ↦ χ (dipoleLift q) * ddVirialField₂ q) u ux uy p *
          (starRingEnd ℂ) (e p)).re) +
      ∫ p in cellSquare, deriv χ (dipoleLift p) *
        (ddGreenNormalFlux u ux uy p - ddWeight p * ddVirialQ (dipoleLift p) *
          (e p * (starRingEnd ℂ) (u p)).re) := by
  obtain ⟨V, hV, hVc, hVU, hsupp⟩ := green_cutoff_patch hc hχs
  have hVC : closure V ⊆ cellSquare := fun p hp ↦ (hVU hp).1
  have hVR : V ⊆ ddRegularCell := subset_closure.trans hVU
  obtain ⟨D, hj, hD, v, hv, hvlim, mOp, _, tOp⟩ :=
    hop.local_smooth_approximation hu hV hVc hVC
  let μ := volume.restrict V
  have hae := hop.ae_eq_jet hV (subset_closure.trans hVC) hj
  have hx : ux =ᵐ[μ] D [0] :=
    (ae_restrict_iff' hV.measurableSet).mpr
      (hae.mono fun p hp hpV ↦ (hp hpV).1)
  have hy : uy =ᵐ[μ] D [1] :=
    (ae_restrict_iff' hV.measurableSet).mpr
      (hae.mono fun p hp hpV ↦ (hp hpV).2.1)
  have mu : MemLp u 2 μ := by simpa only [hj.1] using hD [] (by simp)
  have me : MemLp e 2 μ := he V hV hVc hVC
  have mx : MemLp ux 2 μ := (hD [0] (by simp)).ae_eq hx.symm
  have my : MemLp uy 2 μ := (hD [1] (by simp)).ae_eq hy.symm
  have mv (n) : MemLp (v n) 2 μ := (hvlim [] (by simp)).1 n
  have mvx (n) : MemLp (partialX (v n)) 2 μ := by
    simpa [classicalComplexJet, coordPartial] using (hvlim [0] (by simp)).1 n
  have mvy (n) : MemLp (partialY (v n)) 2 μ := by
    simpa [classicalComplexJet, coordPartial] using (hvlim [1] (by simp)).1 n
  have tu : Tendsto (fun n ↦ eLpNorm (fun p ↦ v n p - u p) 2 μ) atTop (𝓝 0) := by
    simpa only [classicalComplexJet, hj.1] using (hvlim [] (by simp)).2
  have tx : Tendsto (fun n ↦ eLpNorm (fun p ↦ partialX (v n) p - ux p) 2 μ)
      atTop (𝓝 0) := by
    have heq (n) : eLpNorm (fun p ↦ partialX (v n) p - ux p) 2 μ =
        eLpNorm (fun p ↦ classicalComplexJet [0] (v n) p - D [0] p) 2 μ :=
      eLpNorm_congr_ae (hx.mono fun p hp ↦ congrArg (fun c ↦ partialX (v n) p - c) hp)
    simpa only [heq] using (hvlim [0] (by simp)).2
  have ty : Tendsto (fun n ↦ eLpNorm (fun p ↦ partialY (v n) p - uy p) 2 μ)
      atTop (𝓝 0) := by
    have heq (n) : eLpNorm (fun p ↦ partialY (v n) p - uy p) 2 μ =
        eLpNorm (fun p ↦ classicalComplexJet [1] (v n) p - D [1] p) 2 μ :=
      eLpNorm_congr_ae (hy.mono fun p hp ↦ congrArg (fun c ↦ partialY (v n) p - c) hp)
    simpa only [heq] using (hvlim [1] (by simp)).2
  let z := fun n p ↦ ![v n p, ddOperator (v n) p, partialX (v n) p, partialY (v n) p]
  let Z := fun p ↦ ![u p, e p, ux p, uy p]
  have mz (i : Fin 4) (n) : MemLp (fun p ↦ z n p i) 2 μ := by
    fin_cases i
    · exact mv n
    · exact mOp n
    · exact mvx n
    · exact mvy n
  have mZ (i : Fin 4) : MemLp (fun p ↦ Z p i) 2 μ := by
    fin_cases i
    · exact mu
    · exact me
    · exact mx
    · exact my
  have tz (i : Fin 4) :
      Tendsto (fun n ↦ eLpNorm (fun p ↦ z n p i - Z p i) 2 μ) atTop (𝓝 0) := by
    fin_cases i
    · exact tu
    · exact tOp
    · exact tx
    · exact ty
  have mc (k i j : Fin 4) : MemLp (fun p ↦ greenCoefficients χ p k i j) ⊤ μ := by
    have hC := (green_coefficients_continuous hχ k i j).mono hVU
    obtain ⟨C, hCbound⟩ := hVc.exists_bound_of_continuousOn hC
    exact memLp_top_of_bound
      ((hC.mono subset_closure).aestronglyMeasurable hV.measurableSet) C
      (ae_restrict_of_forall_mem hV.measurableSet
        (fun p hp ↦ hCbound p (subset_closure hp)))
  have tl (k : Fin 4) :
      Tendsto (fun n ↦ ∫ p in cellSquare, greenIntegrands χ (v n) (ddOperator (v n))
        (partialX (v n)) (partialY (v n)) p k) atTop
        (𝓝 (∫ p in cellSquare, greenIntegrands χ u e ux uy p k)) := by
    simp_rw [green_integral_localize hχ hχs hV hVR hsupp]
    exact (green_quadratic_limit (mc k) mz mZ tz).2.2
  have hclass (n) :
      (∫ p in cellSquare, greenIntegrands χ (v n) (ddOperator (v n))
        (partialX (v n)) (partialY (v n)) p 0) =
      (∫ p in cellSquare, greenIntegrands χ (v n) (ddOperator (v n))
        (partialX (v n)) (partialY (v n)) p 1) +
      2 * (∫ p in cellSquare, greenIntegrands χ (v n) (ddOperator (v n))
        (partialX (v n)) (partialY (v n)) p 2) +
      (∫ p in cellSquare, greenIntegrands χ (v n) (ddOperator (v n))
        (partialX (v n)) (partialY (v n)) p 3) :=
    dd_smooth_green (hv n).1 (hv n).2.1 (hv n).2.2 hχ hχs
  have tr := ((tl 1).add ((tl 2).const_mul 2)).add (tl 3)
  have hseq :
      (fun n ↦ (∫ p in cellSquare, greenIntegrands χ (v n) (ddOperator (v n))
        (partialX (v n)) (partialY (v n)) p 1) +
      2 * (∫ p in cellSquare, greenIntegrands χ (v n) (ddOperator (v n))
        (partialX (v n)) (partialY (v n)) p 2) +
      (∫ p in cellSquare, greenIntegrands χ (v n) (ddOperator (v n))
        (partialX (v n)) (partialY (v n)) p 3)) =
      (fun n ↦ ∫ p in cellSquare, greenIntegrands χ (v n) (ddOperator (v n))
        (partialX (v n)) (partialY (v n)) p 0) := funext fun n ↦ (hclass n).symm
  rw [hseq] at tr
  exact tendsto_nhds_unique (tl 0) tr

/-- A compact-level cutoff identity determines the virial on every annulus outside
    one common null set. The bulk and boundary densities need only be integrable
    on closed level bands; no positivity or smooth representatives are required. -/
theorem annular_virial_of_cutoff_identity {J B : ℝ × ℝ → ℝ}
    (hJ : ∀ a b : ℝ, 0 < a → b < 1 →
      IntegrableOn J {p | p ∈ cellSquare ∧ 2 * a ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * b})
    (hB : ∀ a b : ℝ, 0 < a → b < 1 →
      IntegrableOn B {p | p ∈ cellSquare ∧ 2 * a ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * b})
    (hcut : ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      ∀ a b : ℝ, 0 < a → b < 1 → (∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) →
        (∫ p in cellSquare, φ (dipoleLift p / 2) * J p) =
          ∫ p in cellSquare, deriv φ (dipoleLift p / 2) / 2 * B p) :
    ∃ N : Set ℝ, volume N = 0 ∧
      ∀ h h' : ℝ, 0 < h → h < h' → h' < 1 → h ∉ N → h' ∉ N →
        (∫ p in {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p ∧ dipoleLift p < 2 * h'}, J p) =
          levelIntegral h B - levelIntegral h' B := by
  have hΨ : Measurable dipoleLift := by unfold dipoleLift; fun_prop
  have hderiv_supp {φ : ℝ → ℝ} {a b : ℝ} (hsupp : ∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) :
      ∀ s, deriv φ s ≠ 0 → a ≤ s ∧ s ≤ b := by
    intro s hs
    by_contra hns
    apply hs
    have hev : φ =ᶠ[𝓝 s] fun _ ↦ 0 := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds (show s ∉ Icc a b from hns)] with t ht
      by_contra hne
      exact ht (hsupp t hne)
    rw [hev.deriv_eq, deriv_const]
  have hbound {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ}
      (hsupp : ∀ s, g s ≠ 0 → a ≤ s ∧ s ≤ b) :
      ∃ C, ∀ s, |g s| ≤ C := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hg.continuousOn (s := Icc a b))
    refine ⟨max C 0, fun s ↦ ?_⟩
    by_cases hs : g s = 0
    · simp [hs]
    · exact (show |g s| ≤ C by simpa using hC s (hsupp s hs)).trans (le_max_left _ _)
  have hcompl {g F : ℝ → ℝ} {a b : ℝ} (hsupp : ∀ s, g s ≠ 0 → a ≤ s ∧ s ≤ b) :
      ∫ s, g s * F s = ∫ s in Icc a b, g s * F s := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦ ?_).symm
    have : g s = 0 := by
      by_contra hne
      exact hs (hsupp s hne)
    simp [this]
  have hid : ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      ∀ a b : ℝ, 0 < a → b < 1 → (∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) →
        ∫ s, φ s * (2 * levelIntegral s J) =
          ∫ s, deriv φ s * levelIntegral s B := by
    intro φ hφ a b ha hb hsupp
    have hdc : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
    obtain ⟨C, hC⟩ := hbound hφ.continuous hsupp
    obtain ⟨C', hC'⟩ := hbound hdc (hderiv_supp hsupp)
    have hsupp' : ∀ s, deriv φ s / 2 ≠ 0 → a ≤ s ∧ s ≤ b := fun s hs ↦
      hderiv_supp hsupp s fun h ↦ hs (by simp [h])
    have hC'' : ∀ s, |deriv φ s / 2| ≤ C' / 2 := fun s ↦ by
      rw [abs_div, abs_two]
      exact div_le_div_of_nonneg_right (hC' s) (by norm_num)
    have c1 := integral_cellSquare_level_mul hφ.continuous.measurable hC ha hb hsupp
      (hJ a b ha hb)
    have c2 := integral_cellSquare_level_mul (hdc.measurable.div_const 2) hC'' ha hb hsupp'
      (hB a b ha hb)
    rw [hcompl hsupp, hcompl (hderiv_supp hsupp)]
    calc
      _ = 2 * ∫ s in Icc a b, φ s * levelIntegral s J := by
        rw [← integral_const_mul]; congr 1; funext s; ring
      _ = ∫ p in cellSquare, φ (dipoleLift p / 2) * J p := c1.symm
      _ = ∫ p in cellSquare, deriv φ (dipoleLift p / 2) / 2 * B p :=
        hcut φ hφ a b ha hb hsupp
      _ = 2 * ∫ s in Icc a b, deriv φ s / 2 * levelIntegral s B := c2
      _ = _ := by rw [← integral_const_mul]; congr 1; funext s; ring
  obtain ⟨N, hN, hdbr⟩ := exists_null_sub_eq_intervalIntegral (α := 0) (β := 1)
    (m := fun h ↦ 2 * levelIntegral h J) (G := fun h ↦ levelIntegral h B)
    (fun a b ha hb ↦ (integrableOn_levelIntegral ha hb (hJ a b ha hb)).const_mul 2)
    (fun a b ha hb ↦ integrableOn_levelIntegral ha hb (hB a b ha hb)) hid
  refine ⟨N, hN, fun h h' h0 hh' h'1 hNh hNh' ↦ ?_⟩
  rw [← hdbr h h' h0 hh' h'1 hNh hNh']
  let S := {p | 2 * h < dipoleLift p ∧ dipoleLift p < 2 * h'}
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const hΨ).inter (measurableSet_lt hΨ measurable_const)
  have hind := integral_cellSquare_level_mul
    (φ := (Ioo h h').indicator fun _ ↦ (1 : ℝ)) (measurable_const.indicator measurableSet_Ioo)
    (C := 1) (fun s ↦ by by_cases hs : s ∈ Ioo h h' <;> simp [hs]) h0 h'1
    (fun s hs ↦ ⟨(Set.mem_of_indicator_ne_zero hs).1.le,
      (Set.mem_of_indicator_ne_zero hs).2.le⟩) (hJ h h' h0 h'1)
  have hpt (p) : (Ioo h h').indicator (fun _ ↦ (1 : ℝ)) (dipoleLift p / 2) * J p =
      S.indicator J p := by
    by_cases hp : p ∈ S
    · rw [indicator_of_mem (show dipoleLift p / 2 ∈ Ioo h h' from
        ⟨by linarith [hp.1], by linarith [hp.2]⟩), indicator_of_mem hp, one_mul]
    · rw [indicator_of_notMem (show dipoleLift p / 2 ∉ Ioo h h' from
        fun hm ↦ hp ⟨by linarith [hm.1], by linarith [hm.2]⟩), indicator_of_notMem hp, zero_mul]
  have hst (s) : (Ioo h h').indicator (fun _ ↦ (1 : ℝ)) s * levelIntegral s J =
      (Ioo h h').indicator (fun s ↦ levelIntegral s J) s := by
    by_cases hs : s ∈ Ioo h h' <;> simp [hs]
  simp_rw [hpt, hst] at hind
  rw [integral_indicator hS, Measure.restrict_restrict hS, integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2 Ioo_subset_Icc_self] at hind
  have hset : {p | p ∈ cellSquare ∧ 2 * h < dipoleLift p ∧ dipoleLift p < 2 * h'} =
      S ∩ cellSquare := by ext p; simp only [S, mem_ofPred_eq, mem_inter_iff]; tauto
  rw [hset, hind, intervalIntegral.integral_of_le hh'.le, integral_Ioc_eq_integral_Ioo,
    integral_const_mul]

/-! ### Positive-level regularity and bulk integrability -/

/-- Positive truncations are open. -/
theorem isOpen_ddTruncatedCell (a : ℝ) : IsOpen (ddTruncatedCell a) := by
  have hc : IsOpen cellSquare := by
    exact (isOpen_lt (show Continuous (fun p : ℝ × ℝ ↦ |(diagCoord p).1|)
      by unfold diagCoord; fun_prop) continuous_const).inter
      (isOpen_lt (show Continuous (fun p : ℝ × ℝ ↦ |(diagCoord p).2|)
        by unfold diagCoord; fun_prop) continuous_const)
  exact hc.inter (isOpen_lt continuous_const
    (show Continuous dipoleLift by unfold dipoleLift; fun_prop))

/-- Smooth division preserves both available stream derivatives on a positive
    truncation, including its elliptic center, without a global divided domain. -/
theorem ddStreamQuotient_memSobolevOn_of_le (ω : L2) {k : ℕ} (hk : k ≤ 2)
    {a : ℝ} (ha : 0 < a) : MemSobolevOn k (ddTruncatedCell a) (ddStreamQuotient ω) := by
  have hs : MemSobolev (k : ℝ) (invLap ω) :=
    (memSobolev_two_invLap ω).mono (by exact_mod_cast hk)
  have hb : Bornology.IsBounded cellNeighbourhood := isBounded_cellNeighbourhood
  have hh : MemSobolevOn k cellNeighbourhood (liftL2 (invLap ω)) := by
    exact memSobolevOn_liftL2 (k := k) (g := invLap ω) (U := cellNeighbourhood)
      (by simpa using hs) hb
  have hc : MemSobolevOn k cellNeighbourhood (contStream ω) :=
    MemSobolevOn.congr_ae (k := k) (U := cellNeighbourhood)
      (g := liftL2 (invLap ω)) (g' := contStream ω) hh (streamLift_ae_eq_contStream ω)
  let U := cellNeighbourhood ∩ {p | 0 < dipoleLift p}
  have hU : IsOpen U := isOrbitUnion_cellNeighbourhood.1.inter
    (isOpen_lt continuous_const
      (show Continuous dipoleLift by unfold dipoleLift; fun_prop))
  have hloc : MemSobolevLocOn k U (contStream ω) :=
    (MemSobolevOn.memSobolevLocOn (k := k) hc).mono inter_subset_left
  have hd : MemSobolevLocOn k U (ddStreamQuotient ω) :=
    hloc.div_smooth hU (by unfold dipoleLift; fun_prop) (fun _ hp ↦ hp.2.ne')
  have hbound : Bornology.IsBounded cellSquare :=
    hb.subset (subset_closure.trans closure_cellSquare_subset_cellNeighbourhood)
  have hclosure : closure (ddTruncatedCell a) ⊆ U := by
    intro p hp
    refine ⟨closure_cellSquare_subset_cellNeighbourhood
      (closure_mono (fun _ h ↦ h.1) hp), ?_⟩
    have hle : a ≤ dipoleLift p :=
      closure_minimal (fun _ h ↦ h.2.le)
        (isClosed_le continuous_const
          (show Continuous dipoleLift by unfold dipoleLift; fun_prop)) hp
    exact ha.trans_le hle
  exact hd _ (isOpen_ddTruncatedCell a)
    (hbound.subset (fun _ hp ↦ hp.1)).isCompact_closure hclosure

/-- Local H² division on the open cell, with no global divided Sobolev domain. -/
theorem ddStreamQuotient_memSobolevLocOn (ω : L2) :
    MemSobolevLocOn 2 cellSquare (ddStreamQuotient ω) := by
  have hs := memSobolev_two_invLap ω
  have hh : MemSobolevOn 2 cellNeighbourhood (liftL2 (invLap ω)) :=
    memSobolevOn_liftL2 (k := 2) (g := invLap ω) (U := cellNeighbourhood)
      (by simpa using hs) isBounded_cellNeighbourhood
  have hc : MemSobolevOn 2 cellNeighbourhood (contStream ω) :=
    MemSobolevOn.congr_ae (k := 2) hh (streamLift_ae_eq_contStream ω)
  have hl : MemSobolevLocOn 2 cellSquare (contStream ω) :=
    (MemSobolevOn.memSobolevLocOn (k := 2) hc).mono
      (subset_closure.trans closure_cellSquare_subset_cellNeighbourhood)
  exact hl.div_smooth isOpen_cellSquare (by unfold dipoleLift; fun_prop) fun p hp ↦
    ne_of_gt (by simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp)

/-- Local L² division of the original vorticity on the open cell. -/
theorem ddVorticityQuotient_memSobolevLocOn (ω : L2) :
    MemSobolevLocOn 0 cellSquare (ddVorticityQuotient ω) := by
  have hh : MemSobolevOn 0 cellNeighbourhood (liftL2 ω) :=
    memLp_liftL2 ω isBounded_cellNeighbourhood
  have hl : MemSobolevLocOn 0 cellSquare (liftL2 ω) :=
    (MemSobolevOn.memSobolevLocOn (k := 0) hh).mono
      (subset_closure.trans closure_cellSquare_subset_cellNeighbourhood)
  exact hl.div_smooth isOpen_cellSquare (by unfold dipoleLift; fun_prop) fun p hp ↦
    ne_of_gt (by simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp)

/-- H¹ regularity on positive truncations. -/
theorem ddStreamQuotient_memSobolevOn (ω : L2) {a : ℝ} (ha : 0 < a) :
    MemSobolevOn 1 (ddTruncatedCell a) (ddStreamQuotient ω) :=
  ddStreamQuotient_memSobolevOn_of_le ω (by norm_num) ha

/-- H² regularity on positive truncations. -/
theorem ddStreamQuotient_memSobolevOn_two (ω : L2) {a : ℝ} (ha : 0 < a) :
    MemSobolevOn 2 (ddTruncatedCell a) (ddStreamQuotient ω) :=
  ddStreamQuotient_memSobolevOn_of_le ω (by norm_num) ha

/-- Arbitrary weak-derivative witnesses inherit H¹ regularity from the H² quotient. -/
theorem ddStreamQuotient_memSobolevOn_derivative {ω : L2} {j : Fin 2}
    {d : ℝ × ℝ → ℂ} (hd : HasWeakPartialOn cellSquare j (ddStreamQuotient ω) d)
    {a : ℝ} (ha : 0 < a) : MemSobolevOn 1 (ddTruncatedCell a) d := by
  obtain ⟨d', hd', hi⟩ := (ddStreamQuotient_memSobolevOn_two ω ha).2 j
  exact MemSobolevOn.congr_ae_on (k := 1) hi (isOpen_ddTruncatedCell a).measurableSet
    (hd'.ae_eq (isOpen_ddTruncatedCell a) (hd.mono (fun _ hp ↦ hp.1)))

/-- Arbitrary weak-derivative witnesses are square integrable above positive levels. -/
theorem ddStreamQuotient_memLp_derivative {ω : L2} {j : Fin 2}
    {d : ℝ × ℝ → ℂ} (hd : HasWeakPartialOn cellSquare j (ddStreamQuotient ω) d)
    {a : ℝ} (ha : 0 < a) :
    MemLp d 2 (volume.restrict (ddTruncatedCell a)) :=
  (ddStreamQuotient_memSobolevOn_derivative hd ha).1

/-- Multiplying back by Ψ identifies arbitrary weak quotient derivatives with the
    original Fourier stream derivatives, without differentiating a representative. -/
theorem ddStreamQuotient_weakPartial_eq {ω : L2} {j : Fin 2} {d : ℝ × ℝ → ℂ}
    (hd : HasWeakPartialOn cellSquare j (ddStreamQuotient ω) d) :
    ∀ᵐ p, p ∈ cellSquare →
      coordPartial j (fun q ↦ (dipoleLift q : ℂ)) p * ddStreamQuotient ω p +
        (dipoleLift p : ℂ) * d p = liftL2 (streamPartial j ω) p := by
  have hp := hd.mul_smooth isOpen_cellSquare
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q ↦ (dipoleLift q : ℂ)) from
      Complex.ofRealCLM.contDiff.comp
        ((Real.contDiff_cos.comp contDiff_fst).add (Real.contDiff_cos.comp contDiff_snd)))
  have heq : ∀ᵐ p : ℝ × ℝ, p ∈ cellSquare →
      (dipoleLift p : ℂ) * ddStreamQuotient ω p = contStream ω p :=
    Eventually.of_forall fun p hp ↦ by
      have hs : dipoleLift p ≠ 0 := ne_of_gt (by
        simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp)
      have hsC : (dipoleLift p : ℂ) ≠ 0 := by exact_mod_cast hs
      dsimp [ddStreamQuotient]
      field_simp
  have hp' := hp.congr_ae_on isOpen_cellSquare.measurableSet heq
    (Eventually.of_forall fun _ _ ↦ rfl)
  have ht := (hasWeakPartialOn_liftL2 (hasFourierPartial_streamPartial ω j)
    cellSquare).congr_left (streamLift_ae_eq_contStream ω)
  exact hp'.ae_eq isOpen_cellSquare ht

/-- The weighted generator of the raw quotient is the ordinary generator of the
    original stream, for every supplied weak gradient and smooth real field. -/
theorem ddWeightedGenerator_raw_ae (ω : L2) {ux uy : ℝ × ℝ → ℂ}
    (hx : HasWeakPartialOn cellSquare 0 (ddStreamQuotient ω) ux)
    (hy : HasWeakPartialOn cellSquare 1 (ddStreamQuotient ω) uy)
    {W₁ W₂ : ℝ × ℝ → ℝ} (hW₁ : Differentiable ℝ W₁) (hW₂ : Differentiable ℝ W₂) :
    ∀ᵐ p, p ∈ cellSquare →
      (dipoleLift p : ℂ) * ddWeightedGenerator W₁ W₂ (ddStreamQuotient ω) ux uy p =
        (W₁ p : ℂ) * liftL2 (streamPartial 0 ω) p +
          (W₂ p : ℂ) * liftL2 (streamPartial 1 ω) p +
          ((divergence W₁ W₂ p / 2 : ℝ) : ℂ) * liftL2 (invLap ω) p := by
  have hΨ : Differentiable ℝ dipoleLift := by unfold dipoleLift; fun_prop
  have hcx : coordPartial (0 : Fin 2) (fun q ↦ (dipoleLift q : ℂ)) =
      fun p ↦ -(Real.sin p.1 : ℂ) := by
    simp [coordPartial, partialX_ofReal hΨ, partialX_dipoleLift]
  have hcy : coordPartial (1 : Fin 2) (fun q ↦ (dipoleLift q : ℂ)) =
      fun p ↦ -(Real.sin p.2 : ℂ) := by
    simp [coordPartial, partialY_ofReal hΨ, partialY_dipoleLift]
  filter_upwards [ddStreamQuotient_weakPartial_eq hx, ddStreamQuotient_weakPartial_eq hy,
    streamLift_ae_eq_contStream ω] with p hdx hdy hv hp
  have hs : dipoleLift p ≠ 0 := ne_of_gt (by
    simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp)
  have hsC : (dipoleLift p : ℂ) ≠ 0 := by exact_mod_cast hs
  have hu : (dipoleLift p : ℂ) * ddStreamQuotient ω p = liftL2 (invLap ω) p := by
    change (dipoleLift p : ℂ) * (contStream ω p / (dipoleLift p : ℂ)) = _
    rw [← hv]
    field_simp
    rfl
  exact ddWeightedGenerator_conjugation (hW₁ p) (hW₂ p) hs hu
    (by simpa only [hcx] using hdx hp) (by simpa only [hcy] using hdy hp)

section WeightedFirst

open scoped ContDiff

/-- Annular cutoffs of the weighted field are smooth periodic adapted fields.
    Multiplication of the ordinary normal field by a level factor gives the
    weighted field, including the totalized values on singular levels. -/
theorem annularCutoff_ddVirialField {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {a b : ℝ} (ha : 0 < a) (hb : b < 2)
    (hχ0 : ∀ s, χ s ≠ 0 → a ≤ s ∧ s ≤ b) :
    ContDiff ℝ ∞ (fun p ↦ χ (dipoleLift p) * ddVirialField₁ p) ∧
    ContDiff ℝ ∞ (fun p ↦ χ (dipoleLift p) * ddVirialField₂ p) ∧
    ContDiff ℝ ∞ (fun p ↦ χ (dipoleLift p) * ddVirialCoeff p) ∧
    IsPeriodicLift (fun p ↦ χ (dipoleLift p) * ddVirialField₁ p) ∧
    IsPeriodicLift (fun p ↦ χ (dipoleLift p) * ddVirialField₂ p) ∧
    IsPeriodicLift (fun p ↦ χ (dipoleLift p) * ddVirialCoeff p) ∧
    IsAdaptedOn (fun p ↦ χ (dipoleLift p) * ddVirialField₁ p)
      (fun p ↦ χ (dipoleLift p) * ddVirialField₂ p)
      (fun p ↦ χ (dipoleLift p) * ddVirialCoeff p) univ := by
  let κ := fun s ↦ χ s * (s ^ 2 + 2 * s + 4) / (3 * s ^ 2)
  have hκ : ContDiff ℝ ∞ κ := by
    apply contDiff_iff_contDiffAt.mpr
    intro s
    by_cases hs : s = 0
    · subst s
      apply contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds ha] with t ht
      have hz : χ t = 0 := by
        by_contra hn
        exact (not_le.mpr ht) (hχ0 t hn).1
      simp [κ, hz]
    · dsimp only [κ]
      exact (hχ.contDiffAt.mul (by fun_prop)).div (by fun_prop) (by simp [hs])
  have hκ0 : ∀ s, κ s ≠ 0 → a ≤ s ∧ s ≤ b := by
    intro s hs
    apply hχ0 s
    intro hz
    exact hs (by simp [κ, hz])
  have h₁ : (fun p ↦ κ (dipoleLift p) * normalField₁ p) =
      fun p ↦ χ (dipoleLift p) * ddVirialField₁ p := by
    funext p
    unfold normalField₁ ddVirialField₁ ddVirialQ κ
    simp only [div_eq_mul_inv]
    ring
  have h₂ : (fun p ↦ κ (dipoleLift p) * normalField₂ p) =
      fun p ↦ χ (dipoleLift p) * ddVirialField₂ p := by
    funext p
    unfold normalField₂ ddVirialField₂ ddVirialQ κ
    simp only [div_eq_mul_inv]
    ring
  have hf : (fun p ↦ κ (dipoleLift p) * normalCoeff p) =
      fun p ↦ χ (dipoleLift p) * ddVirialCoeff p := by
    funext p
    unfold normalCoeff ddVirialCoeff ddF ddWeight κ
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simpa only [h₁, h₂, hf] using annularCutoff_normalField hκ ha hb hκ0

private theorem first_virial_on_cell {W₁ W₂ f : ℝ × ℝ → ℝ}
    (had : IsAdaptedOn W₁ W₂ f univ)
    (hW₁ : ContDiff ℝ 2 W₁) (hW₂ : ContDiff ℝ 2 W₂) (hf : ContDiff ℝ 1 f)
    (hp₁ : IsPeriodicLift W₁) (hp₂ : IsPeriodicLift W₂) (hpf : IsPeriodicLift f)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    (hsupp : ∀ p, W₁ p ≠ 0 ∨ W₂ p ≠ 0 ∨ f p ≠ 0 →
      2 * a ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * b)
    {lam : ℝ} (hlam : lam ≠ 0) {v : L2} (hv : IsEigenSolution lam v) :
    (∫ p in cellSquare, (f p • liftL2 v p *
      (starRingEnd ℂ) (liftL2 v p + streamLift v p)).re) =
    2 * ∫ p in cellSquare,
      ((W₁ p • streamLiftX v p + W₂ p • streamLiftY v p +
        ((1 / 2 : ℝ) * divergence W₁ W₂ p) • streamLift v p) *
          (starRingEnd ℂ) (liftL2 v p)).re := by
  let D := fun p ↦ W₁ p • streamLiftX v p + W₂ p • streamLiftY v p +
    ((1 / 2 : ℝ) * divergence W₁ W₂ p) • streamLift v p
  let A := fun p ↦ (f p • liftL2 v p *
    (starRingEnd ℂ) (liftL2 v p + streamLift v p)).re
  let B := fun p ↦ (D p * (starRingEnd ℂ) (liftL2 v p)).re
  have hdc : Continuous (divergence W₁ W₂) :=
    (continuous_partialX_real (hW₁.of_le (by norm_num))).add
      (continuous_partialY_real (hW₂.of_le (by norm_num)))
  have hpdiv : IsPeriodicLift (divergence W₁ W₂) := hp₁.partialX.add hp₂.partialY
  have hiA : IntegrableOn (fun p ↦ f p • liftL2 v p *
      (starRingEnd ℂ) (liftL2 v p + streamLift v p)) periodSquare := by
    convert (integrableOn_smul_liftL2_mul_conj hf.continuous hpf v v).add
      (integrableOn_smul_liftL2_mul_conj hf.continuous hpf v (invLap v)) using 1
    ext p
    simp only [streamLift, map_add, mul_add, Pi.add_apply]
  have hiB : IntegrableOn (fun p ↦ D p * (starRingEnd ℂ) (liftL2 v p)) periodSquare := by
    convert ((integrableOn_smul_liftL2_mul_conj hW₁.continuous hp₁ (streamPartial 0 v) v).add
      (integrableOn_smul_liftL2_mul_conj hW₂.continuous hp₂ (streamPartial 1 v) v)).add
      (integrableOn_smul_liftL2_mul_conj (continuous_const.mul hdc)
        (hpdiv.const_mul (1 / 2)) (invLap v) v) using 1
    ext p
    simp only [D, streamLift, streamLiftX, streamLiftY, add_mul, Pi.add_apply, Pi.mul_apply]
  have heA : (squarePairing (fun p ↦ f p • liftL2 v p)
      (fun p ↦ liftL2 v p + streamLift v p)).re = squareIntegral A := by
    exact (integral_re hiA).symm
  have heB : (squarePairing D (liftL2 v)).re = squareIntegral B := by
    exact (integral_re hiB).symm
  have hfirst := virial_l2_first had hW₁ hW₂ hf hp₁ hp₂ hpf ha hb hsupp hlam hv
  change (squarePairing _ _).re = 2 * (squarePairing D (liftL2 v)).re at hfirst
  rw [heA, heB] at hfirst
  have hm (g : L2) : Measurable (liftL2 g) :=
    (Lp.stronglyMeasurable g).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable
  have hfm := hf.continuous.measurable
  have hxm := hW₁.continuous.measurable
  have hym := hW₂.continuous.measurable
  have hmA : Measurable A := by
    dsimp only [A, streamLift]
    fun_prop
  have hmB : Measurable B := by
    dsimp only [B, D, streamLiftX, streamLiftY, streamLift]
    fun_prop
  have hpA : IsPeriodicLift A := by
    intro p
    have hu := isPeriodicLift_liftL2 v p
    have hv := isPeriodicLift_liftL2 (invLap v) p
    constructor <;> simp only [A, streamLift, (hpf p).1, (hpf p).2, hu.1, hu.2, hv.1, hv.2]
  have hpB : IsPeriodicLift B := by
    intro p
    have hu := isPeriodicLift_liftL2 v p
    have hv := isPeriodicLift_liftL2 (invLap v) p
    have hx := isPeriodicLift_liftL2 (streamPartial 0 v) p
    have hy := isPeriodicLift_liftL2 (streamPartial 1 v) p
    constructor <;> simp only [B, D, streamLiftX, streamLiftY, streamLift,
      (hp₁ p).1, (hp₁ p).2, (hp₂ p).1, (hp₂ p).2, (hpdiv p).1, (hpdiv p).2,
      hu.1, hu.2, hv.1, hv.2, hx.1, hx.2, hy.1, hy.2]
  have hzero {p : ℝ × ℝ} (hp : dipoleLift p < 2 * a) :
      W₁ p = 0 ∧ W₂ p = 0 ∧ f p = 0 := by
    have hn : ¬ (W₁ p ≠ 0 ∨ W₂ p ≠ 0 ∨ f p ≠ 0) :=
      fun h ↦ (not_le.mpr hp) (hsupp p h).1
    simpa only [not_or, ne_eq, not_not] using hn
  have hB0 : ∀ p, dipoleLift p ≤ 0 → B p = 0 := by
    intro p hp
    have hz := hzero (p := p) (by linarith)
    have hev : ∀ᶠ q in 𝓝 p, W₁ q = 0 ∧ W₂ q = 0 ∧ f q = 0 := by
      have hn : {q : ℝ × ℝ | dipoleLift q < 2 * a} ∈ 𝓝 p :=
        (isOpen_lt (show Continuous dipoleLift by unfold dipoleLift; fun_prop)
          continuous_const).mem_nhds (by change dipoleLift p < 2 * a; linarith)
      filter_upwards [hn] with q hq
      exact hzero hq
    have hd : divergence W₁ W₂ p = 0 := by
      simp [divergence, partialX_eq_zero_of_eventually (hev.mono fun q hq ↦ hq.1),
        partialY_eq_zero_of_eventually (hev.mono fun q hq ↦ hq.2.1)]
    simp [B, D, hz.1, hz.2.1, hd]
  have hA0 : ∀ p, dipoleLift p ≤ 0 → A p = 0 := by
    intro p hp
    simp [A, (hzero (p := p) (by linarith)).2.2]
  rw [squareIntegral_eq_setIntegral_cellSquare hpA hmA hA0,
    squareIntegral_eq_setIntegral_cellSquare hpB hmB hB0] at hfirst
  exact hfirst

private theorem weighted_pair_cancel (s : ℝ) (z w : ℂ) :
    s ^ 2 * (z * (starRingEnd ℂ) w).re =
      ((s : ℂ) * z * (starRingEnd ℂ) ((s : ℂ) * w)).re := by
  have he : (s : ℂ) * z * (starRingEnd ℂ) ((s : ℂ) * w) =
      ((s ^ 2 : ℝ) : ℂ) * (z * (starRingEnd ℂ) w) := by
    simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_pow]
    ring
  rw [he, Complex.re_ofReal_mul]

end WeightedFirst

set_option linter.unusedVariables false in
/-- Weighted first identity with annular cutoff, on the original eigenfunction domain.
    Only local weak derivatives of the raw stream quotient are supplied.
    Conjugation uses the weak product rule, not the quotient equation or parity. -/
theorem dd_weighted_first {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    {ux uy : ℝ × ℝ → ℂ}
    (hx : HasWeakPartialOn cellSquare 0 (ddStreamQuotient ω) ux)
    (hy : HasWeakPartialOn cellSquare 1 (ddStreamQuotient ω) uy)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (0 : ℝ) 2) :
    (∫ p in cellSquare, ddWeight p * χ (dipoleLift p) * ddVirialCoeff p *
      (ddVorticityQuotient ω p * (starRingEnd ℂ)
        (ddVorticityQuotient ω p + ddStreamQuotient ω p)).re) =
    2 * ∫ p in cellSquare, ddWeight p *
      (ddWeightedGenerator (fun q ↦ χ (dipoleLift q) * ddVirialField₁ q)
        (fun q ↦ χ (dipoleLift q) * ddVirialField₂ q)
        (ddStreamQuotient ω) ux uy p * (starRingEnd ℂ) (ddVorticityQuotient ω p)).re := by
  obtain ⟨a, ha, hlo⟩ := hc.exists_forall_le' continuous_id.continuousOn
    (fun s hs ↦ (hχs hs).1)
  obtain ⟨δ, hδ, hhi⟩ := hc.exists_forall_le' (f := fun s : ℝ ↦ 2 - s) (a := 0)
    (continuous_const.sub continuous_id).continuousOn
    (fun s hs ↦ by linarith [(hχs hs).2])
  let b := 2 - δ
  have hb : b < 2 := by dsimp [b]; linarith
  have hband : ∀ s, χ s ≠ 0 → a ≤ s ∧ s ≤ b := by
    intro s hs
    have ht := subset_tsupport χ hs
    exact ⟨hlo s ht, by dsimp [b]; linarith [hhi s ht]⟩
  let X := fun p ↦ χ (dipoleLift p) * ddVirialField₁ p
  let Y := fun p ↦ χ (dipoleLift p) * ddVirialField₂ p
  let F := fun p ↦ χ (dipoleLift p) * ddVirialCoeff p
  let D := fun p ↦ X p • streamLiftX ω p + Y p • streamLiftY ω p +
    ((1 / 2 : ℝ) * divergence X Y p) • streamLift ω p
  obtain ⟨hX, hY, hF, hpX, hpY, hpF, had⟩ := annularCutoff_ddVirialField hχ ha hb hband
  have hsupp : ∀ p, X p ≠ 0 ∨ Y p ≠ 0 ∨ F p ≠ 0 →
      2 * (a / 2) ≤ dipoleLift p ∧ dipoleLift p ≤ 2 * (b / 2) := by
    intro p hp
    have hn : χ (dipoleLift p) ≠ 0 := by
      rcases hp with hp | hp | hp <;> exact left_ne_zero_of_mul hp
    obtain ⟨hl, hu⟩ := hband _ hn
    constructor <;> linarith
  have V := first_virial_on_cell had (hX.of_le (by simp)) (hY.of_le (by simp))
    (hF.of_le (by simp)) hpX hpY hpF (by positivity : 0 < a / 2)
    (by linarith : b / 2 < 1) hsupp hlam hω
  change (∫ p in cellSquare, (F p • liftL2 ω p *
    (starRingEnd ℂ) (liftL2 ω p + streamLift ω p)).re) =
      2 * ∫ p in cellSquare, (D p * (starRingEnd ℂ) (liftL2 ω p)).re at V
  have hv (p : ℝ × ℝ) (hp : p ∈ cellSquare) :
      (dipoleLift p : ℂ) * ddVorticityQuotient ω p = liftL2 ω p := by
    have hs : dipoleLift p ≠ 0 := ne_of_gt (by
      simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp)
    have hsC : (dipoleLift p : ℂ) ≠ 0 := by exact_mod_cast hs
    dsimp [ddVorticityQuotient]
    field_simp
  have hgen : ∀ᵐ p, p ∈ cellSquare →
      (dipoleLift p : ℂ) *
        ddWeightedGenerator X Y (ddStreamQuotient ω) ux uy p = D p := by
    have hg := ddWeightedGenerator_raw_ae ω hx hy
      (hX.differentiable (by simp)) (hY.differentiable (by simp))
    filter_upwards [hg] with p hp hcell
    have hh : divergence X Y p / 2 = (1 / 2) * divergence X Y p := by ring
    have he := hp hcell
    change (dipoleLift p : ℂ) * ddWeightedGenerator X Y (ddStreamQuotient ω) ux uy p =
      (X p : ℂ) * streamLiftX ω p + (Y p : ℂ) * streamLiftY ω p +
        ((divergence X Y p / 2 : ℝ) : ℂ) * streamLift ω p at he
    rw [hh] at he
    simpa only [D, Complex.real_smul] using he
  have hl :
      (∫ p in cellSquare, ddWeight p * χ (dipoleLift p) * ddVirialCoeff p *
        (ddVorticityQuotient ω p * (starRingEnd ℂ)
          (ddVorticityQuotient ω p + ddStreamQuotient ω p)).re) =
      ∫ p in cellSquare, (F p • liftL2 ω p *
        (starRingEnd ℂ) (liftL2 ω p + streamLift ω p)).re := by
    apply setIntegral_congr_ae isOpen_cellSquare.measurableSet
    filter_upwards [streamLift_ae_eq_contStream ω] with p hrep hp
    have hs : dipoleLift p ≠ 0 := ne_of_gt (by
      simpa [positiveCell, Ψ_torusProj] using torusProj_mem_positiveCell hp)
    have hsC : (dipoleLift p : ℂ) ≠ 0 := by exact_mod_cast hs
    have hu : (dipoleLift p : ℂ) * ddStreamQuotient ω p = streamLift ω p := by
      rw [hrep]
      dsimp [ddStreamQuotient]
      field_simp
    calc _ = F p * (dipoleLift p ^ 2 *
          (ddVorticityQuotient ω p * (starRingEnd ℂ)
            (ddVorticityQuotient ω p + ddStreamQuotient ω p)).re) := by
           dsimp [F, ddWeight]
           ring
         _ = F p * ((dipoleLift p : ℂ) * ddVorticityQuotient ω p *
           (starRingEnd ℂ) ((dipoleLift p : ℂ) *
             (ddVorticityQuotient ω p + ddStreamQuotient ω p))).re := by
           rw [weighted_pair_cancel]
         _ = F p * (liftL2 ω p *
           (starRingEnd ℂ) (liftL2 ω p + streamLift ω p)).re := by
           rw [mul_add, hv p hp, hu]
         _ = _ := by simp only [Complex.real_smul, mul_assoc, Complex.re_ofReal_mul]
  have hr :
      (∫ p in cellSquare, ddWeight p *
        (ddWeightedGenerator X Y (ddStreamQuotient ω) ux uy p *
          (starRingEnd ℂ) (ddVorticityQuotient ω p)).re) =
      ∫ p in cellSquare, (D p * (starRingEnd ℂ) (liftL2 ω p)).re := by
    apply setIntegral_congr_ae isOpen_cellSquare.measurableSet
    filter_upwards [hgen] with p hg hp
    change dipoleLift p ^ 2 * _ = _
    rw [weighted_pair_cancel, hg hp, hv p hp]
  rw [hl, hr]
  exact V

/-- The apparent center singularities of the bulk coefficients are bounded on
    every positive truncation. Values at `Ψ = 2` are the totalized expressions. -/
theorem dd_coefficients_bound {p : ℝ × ℝ} {a : ℝ} (ha : 0 < a)
    (hp : a < dipoleLift p) :
    |ddF p| ≤ 8 / a ∧ |ddA p| ≤ 8 + 16 / a ∧ |ddC p| ≤ 4 := by
  let s := dipoleLift p
  have hs0 : 0 < s := ha.trans hp
  have hs2 : s ≤ 2 := by
    dsimp only [s, dipoleLift]
    linarith [Real.cos_le_one p.1, Real.cos_le_one p.2]
  have hβ0 : 0 ≤ (s ^ 2 + 2 * s + 4) / 3 := by positivity
  have hβ : (s ^ 2 + 2 * s + 4) / 3 ≤ 4 := by nlinarith
  have hF : ddF p = (s ^ 2 + 2 * s + 4) / 3 * normalCoeff p := by
    unfold ddF normalCoeff
    dsimp only [s]
    ring
  have hC : ddC p = (s ^ 2 + 2 * s + 4) / 3 * normalC p := by
    unfold ddC normalC
    dsimp only [s]
    ring
  have hf : 0 ≤ ddF p ∧ ddF p ≤ 8 / a := by
    rcases lt_or_eq_of_le hs2 with hs | hs
    · have hn := normalCoeff_nonneg hs0 hs
      have hb : normalCoeff p ≤ 2 / a := by
        refine (normalCoeff_le hs0 hs).trans ?_
        apply (div_le_div_iff₀ hs0 ha).mpr
        nlinarith [hp]
      rw [hF]
      refine ⟨mul_nonneg hβ0 hn, ?_⟩
      calc _ ≤ 4 * (2 / a) := mul_le_mul hβ hb hn (by norm_num)
        _ = _ := by ring
    · have hz : ddF p = 0 := by unfold ddF; change s * (8 - s ^ 3) * _ / _ = 0; rw [hs]; norm_num
      rw [hz]
      exact ⟨le_rfl, by positivity⟩
  have hc : 0 ≤ ddC p ∧ ddC p ≤ 4 := by
    rcases lt_or_eq_of_le hs2 with hs | hs
    · obtain ⟨hn, hb⟩ := normalC_pos_le_one hs0 hs
      rw [hC]
      exact ⟨mul_nonneg hβ0 hn.le, (mul_le_mul hβ hb hn.le (by norm_num)).trans_eq (by ring)⟩
    · have hz : ddC p = 0 := by unfold ddC; change s * (8 - s ^ 3) / _ = 0; rw [hs]; norm_num
      rw [hz]
      exact ⟨le_rfl, by norm_num⟩
  have hi : 1 / s ≤ 1 / a := one_div_le_one_div_of_le ha hp.le
  have hs : 0 ≤ 2 * s ^ 2 / 3 := by positivity
  have ht : 0 ≤ 32 / (3 * s) := by positivity
  have hA : |ddA p| ≤ 8 + 16 / a := by
    unfold ddA
    change |2 * s ^ 2 / 3 + 32 / (3 * s) - ddC p| ≤ _
    calc
      _ ≤ (2 * s ^ 2 / 3 + 32 / (3 * s)) + ddC p := by
        have hab := abs_sub (2 * s ^ 2 / 3 + 32 / (3 * s)) (ddC p)
        rw [abs_of_nonneg (add_nonneg hs ht), abs_of_nonneg hc.1] at hab
        exact hab
      _ ≤ _ := by
        have hpow : s ^ 2 ≤ 4 := by nlinarith
        have hb : 32 / (3 * s) ≤ (32 / 3 : ℝ) * (1 / a) := by
          calc _ = (32 / 3 : ℝ) * (1 / s) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hi (by norm_num)
        have hia : 0 ≤ 1 / a := by positivity
        simp only [div_eq_mul_inv] at hb hia ⊢
        nlinarith [hc.2]
  exact ⟨by rw [abs_of_nonneg hf.1]; exact hf.2,
    hA, by rw [abs_of_nonneg hc.1]; exact hc.2⟩

theorem measurable_ddStreamQuotient (ω : L2) : Measurable (ddStreamQuotient ω) := by
  unfold ddStreamQuotient dipoleLift
  have hc := (continuous_contStream ω).measurable
  fun_prop

theorem measurable_ddVorticityQuotient (ω : L2) : Measurable (ddVorticityQuotient ω) := by
  unfold ddVorticityQuotient dipoleLift
  have hm : Measurable (liftL2 ω) := (Lp.stronglyMeasurable ω).measurable.comp
    isOpenQuotientMap_torusProj.continuous.measurable
  fun_prop

/-- The undivided vorticity's L² norm controls division above a positive level. -/
theorem ddVorticityQuotient_memLp (ω : L2) {a : ℝ} (ha : 0 < a) :
    MemLp (ddVorticityQuotient ω) 2 (volume.restrict (ddTruncatedCell a)) := by
  have hb : Bornology.IsBounded (ddTruncatedCell a) :=
    isBounded_cellNeighbourhood.subset (fun _ hp ↦
      closure_cellSquare_subset_cellNeighbourhood (subset_closure hp.1))
  apply ((memLp_liftL2 ω hb).norm.const_mul (1 / a)).mono'
    (measurable_ddVorticityQuotient ω).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (isOpen_ddTruncatedCell a).measurableSet] with p hp
  have hs : 0 < dipoleLift p := ha.trans hp.2
  rw [ddVorticityQuotient, norm_div, Complex.norm_real,
    Real.norm_of_nonneg hs.le]
  have hn := mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le ha hp.2.le)
    (norm_nonneg (liftL2 ω p))
  convert hn using 1
  ring

/-- The normal component of an L² gradient is L² for any measure, including
    totalized values at critical points. -/
theorem memLp_normalDeriv {μ : Measure (ℝ × ℝ)} {ux uy : ℝ × ℝ → ℂ}
    (hx : MemLp ux 2 μ) (hy : MemLp uy 2 μ) : MemLp (normalDeriv ux uy) 2 μ := by
  have msx : Measurable (fun p : ℝ × ℝ ↦ (Real.sin p.1 : ℂ)) := by fun_prop
  have msy : Measurable (fun p : ℝ × ℝ ↦ (Real.sin p.2 : ℂ)) := by fun_prop
  have mi : Measurable (fun p : ℝ × ℝ ↦ (gradNorm p : ℂ)⁻¹) := by
    unfold gradNorm
    fun_prop
  apply (hx.norm.add hy.norm).mono'
    (((msx.aestronglyMeasurable.mul hx.aestronglyMeasurable).add
      (msy.aestronglyMeasurable.mul hy.aestronglyMeasurable)).mul
        mi.aestronglyMeasurable)
  exact Eventually.of_forall (norm_normalDeriv_le ux uy)

/-- The tangential component obeys the same L² estimate. -/
theorem memLp_tangentDeriv {μ : Measure (ℝ × ℝ)} {ux uy : ℝ × ℝ → ℂ}
    (hx : MemLp ux 2 μ) (hy : MemLp uy 2 μ) : MemLp (tangentDeriv ux uy) 2 μ := by
  have msx : Measurable (fun p : ℝ × ℝ ↦ (Real.sin p.1 : ℂ)) := by fun_prop
  have msy : Measurable (fun p : ℝ × ℝ ↦ (Real.sin p.2 : ℂ)) := by fun_prop
  have mi : Measurable (fun p : ℝ × ℝ ↦ (gradNorm p : ℂ)⁻¹) := by
    unfold gradNorm
    fun_prop
  apply (hx.norm.add hy.norm).mono'
    (((msy.aestronglyMeasurable.mul hx.aestronglyMeasurable).sub
      (msx.aestronglyMeasurable.mul hy.aestronglyMeasurable)).mul
        mi.aestronglyMeasurable)
  exact Eventually.of_forall (norm_tangentDeriv_le ux uy)

/-- L² values and first derivatives suffice for absolute integrability of the
    weighted virial bulk on a positive truncation. -/
theorem ddVirialDensity_integrable {u e ux uy : ℝ × ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hu : MemLp u 2 (volume.restrict (ddTruncatedCell a)))
    (he : MemLp e 2 (volume.restrict (ddTruncatedCell a)))
    (hx : MemLp ux 2 (volume.restrict (ddTruncatedCell a)))
    (hy : MemLp uy 2 (volume.restrict (ddTruncatedCell a))) :
    IntegrableOn (ddVirialDensity u e ux uy) (ddTruncatedCell a) := by
  have isq (v : ℝ × ℝ → ℂ) (hv : MemLp v 2 (volume.restrict (ddTruncatedCell a))) :
      IntegrableOn (fun p ↦ ‖v p‖ ^ 2) (ddTruncatedCell a) :=
    (memLp_two_iff_integrable_sq hv.norm.aestronglyMeasurable).mp hv.norm
  have iU := isq u hu
  have iE := isq e he
  have iX := isq ux hx
  have iY := isq uy hy
  have mn := (memLp_normalDeriv hx hy).aestronglyMeasurable
  have mt := (memLp_tangentDeriv hx hy).aestronglyMeasurable
  have mf : Measurable ddF := by
    change Measurable (fun p ↦ ddF p)
    simp only [ddF, gradSq_dipoleLift, dipoleLift]
    fun_prop
  have ma : Measurable ddA := by
    change Measurable (fun p ↦ ddA p)
    simp only [ddA, ddC, gradSq_dipoleLift, dipoleLift]
    fun_prop
  have mc : Measurable ddC := by
    change Measurable (fun p ↦ ddC p)
    simp only [ddC, gradSq_dipoleLift, dipoleLift]
    fun_prop
  have md : AEStronglyMeasurable (ddVirialDensity u e ux uy)
      (volume.restrict (ddTruncatedCell a)) :=
    (mf.aestronglyMeasurable.mul (he.aestronglyMeasurable.norm.pow 2 |>.sub
      (hu.aestronglyMeasurable.norm.pow 2))).add
      ((ma.aestronglyMeasurable.mul (mn.norm.pow 2)).add
        (mc.aestronglyMeasurable.mul (mt.norm.pow 2)))
  apply (((iE.add iU).const_mul (8 / a)).add
    ((iX.add iY).const_mul (24 + 32 / a))).mono' md
  filter_upwards [ae_restrict_mem (isOpen_ddTruncatedCell a).measurableSet] with p hp
  rw [Real.norm_eq_abs]
  obtain ⟨hf, hA, hC⟩ := dd_coefficients_bound ha hp.2
  have hn : ‖normalDeriv ux uy p‖ ^ 2 ≤ 2 * (‖ux p‖ ^ 2 + ‖uy p‖ ^ 2) := by
    have hb := norm_normalDeriv_le ux uy p
    nlinarith [norm_nonneg (normalDeriv ux uy p), norm_nonneg (ux p),
      norm_nonneg (uy p), sq_nonneg (‖ux p‖ - ‖uy p‖)]
  have ht : ‖tangentDeriv ux uy p‖ ^ 2 ≤ 2 * (‖ux p‖ ^ 2 + ‖uy p‖ ^ 2) := by
    have hb := norm_tangentDeriv_le ux uy p
    nlinarith [norm_nonneg (tangentDeriv ux uy p), norm_nonneg (ux p),
      norm_nonneg (uy p), sq_nonneg (‖ux p‖ - ‖uy p‖)]
  have hv : |‖e p‖ ^ 2 - ‖u p‖ ^ 2| ≤ ‖e p‖ ^ 2 + ‖u p‖ ^ 2 := by
    have hb := abs_sub (‖e p‖ ^ 2) (‖u p‖ ^ 2)
    rw [abs_of_nonneg (sq_nonneg (‖e p‖)), abs_of_nonneg (sq_nonneg (‖u p‖))] at hb
    exact hb
  dsimp only [ddVirialDensity, ddMatrixForm]
  calc
    _ ≤ |ddF p * (‖e p‖ ^ 2 - ‖u p‖ ^ 2)| +
        (|ddA p * ‖normalDeriv (fun _ ↦ ux p) (fun _ ↦ uy p) p‖ ^ 2| +
          |ddC p * ‖tangentDeriv (fun _ ↦ ux p) (fun _ ↦ uy p) p‖ ^ 2|) :=
      (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ (8 / a) * (‖e p‖ ^ 2 + ‖u p‖ ^ 2) +
        ((8 + 16 / a) * (2 * (‖ux p‖ ^ 2 + ‖uy p‖ ^ 2)) +
          4 * (2 * (‖ux p‖ ^ 2 + ‖uy p‖ ^ 2))) := by
      simp only [abs_mul, abs_pow, abs_norm]
      gcongr
      · exact hn
      · exact ht
    _ = _ := by dsimp only [Pi.add_apply]; ring

/-- The boundary density is absolutely integrable above each positive level.
    Thus coarea produces locally integrable level terms for arbitrary weak witnesses. -/
theorem ddBoundaryDensity_integrable {u e ux uy : ℝ × ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hu : MemLp u 2 (volume.restrict (ddTruncatedCell a)))
    (he : MemLp e 2 (volume.restrict (ddTruncatedCell a)))
    (hx : MemLp ux 2 (volume.restrict (ddTruncatedCell a)))
    (hy : MemLp uy 2 (volume.restrict (ddTruncatedCell a))) :
    IntegrableOn (ddBoundaryDensity u e ux uy) (ddTruncatedCell a) := by
  have hn : MemLp (ddInwardNormal ux uy) 2 (volume.restrict (ddTruncatedCell a)) :=
    (memLp_normalDeriv hx hy).neg
  have ht := memLp_tangentDeriv hx hy
  have isq (v : ℝ × ℝ → ℂ) (hv : MemLp v 2 (volume.restrict (ddTruncatedCell a))) :
      IntegrableOn (fun p ↦ ‖v p‖ ^ 2) (ddTruncatedCell a) :=
    (memLp_two_iff_integrable_sq hv.norm.aestronglyMeasurable).mp hv.norm
  have ic : IntegrableOn (fun p ↦ ‖ddInwardNormal ux uy p‖ ^ 2 -
      ‖tangentDeriv ux uy p‖ ^ 2 - ‖u p‖ ^ 2 +
      (e p * (starRingEnd ℂ) (u p)).re) (ddTruncatedCell a) :=
    (((isq _ hn).sub (isq _ ht)).sub (isq _ hu)).add (he.integrable_mul hu.star).re
  have il : IntegrableOn (fun p ↦ ((starRingEnd ℂ) (u p) *
      ddInwardNormal ux uy p).re) (ddTruncatedCell a) := (hu.star.integrable_mul hn).re
  have mb : Measurable (fun p ↦ (8 - dipoleLift p ^ 3) / 3) := by
    unfold dipoleLift
    fun_prop
  have ml : Measurable (fun p ↦ dipoleLift p ^ 2 * gradNorm p) := by
    unfold dipoleLift gradNorm
    fun_prop
  have hb : ∀ᵐ p ∂(volume.restrict (ddTruncatedCell a)),
      ‖(8 - dipoleLift p ^ 3) / 3‖ ≤ 8 ∧ ‖dipoleLift p ^ 2 * gradNorm p‖ ≤ 8 := by
    filter_upwards [ae_restrict_mem (isOpen_ddTruncatedCell a).measurableSet] with p hp
    have hs0 : 0 < dipoleLift p := ha.trans hp.2
    have hs2 : dipoleLift p ≤ 2 := by
      unfold dipoleLift
      linarith [Real.cos_le_one p.1, Real.cos_le_one p.2]
    have hg0 : 0 ≤ gradNorm p := Real.sqrt_nonneg _
    have hg2 : gradNorm p ≤ 2 := by
      have hsq : gradNorm p ^ 2 ≤ 2 := by
        rw [gradNorm, Real.sq_sqrt (by positivity)]
        linarith [Real.sin_sq_le_one p.1, Real.sin_sq_le_one p.2]
      nlinarith
    have hs3 : dipoleLift p ^ 3 ≤ 8 := by
      calc _ ≤ (2 : ℝ) ^ 3 := pow_le_pow_left₀ hs0.le hs2 3
        _ = 8 := by norm_num
    constructor
    · rw [Real.norm_of_nonneg (by linarith : 0 ≤ (8 - dipoleLift p ^ 3) / 3)]
      have hs3pos : 0 ≤ dipoleLift p ^ 3 := by positivity
      linarith
    · rw [Real.norm_of_nonneg (by positivity)]
      have hpow : dipoleLift p ^ 2 ≤ 4 := by nlinarith
      nlinarith
  exact (ic.bdd_mul mb.aestronglyMeasurable (hb.mono fun _ h ↦ h.1)).sub
    (il.bdd_mul ml.aestronglyMeasurable (hb.mono fun _ h ↦ h.2))

/-- Once the weak cutoff identity is known, all integrability, coarea, level
    normalization and common-exceptional-set conclusions of the annular virial follow. -/
theorem dd_annular_virial_of_cutoff_identity (ω : L2) {ux uy : ℝ × ℝ → ℂ}
    (hx : HasWeakPartialOn cellSquare 0 (ddStreamQuotient ω) ux)
    (hy : HasWeakPartialOn cellSquare 1 (ddStreamQuotient ω) uy)
    (hcut : ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      ∀ a b : ℝ, 0 < a → b < 1 → (∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) →
        (∫ p in cellSquare, φ (dipoleLift p / 2) *
          ddVirialDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy p) =
        ∫ p in cellSquare, deriv φ (dipoleLift p / 2) / 2 *
          ddBoundaryDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy p) :
    (∀ a b : ℝ, 0 < a → a < b → b < 2 →
      IntegrableOn (ddVirialDensity (ddStreamQuotient ω)
        (fun p ↦ -ddVorticityQuotient ω p) ux uy)
        {p | p ∈ cellSquare ∧ a < dipoleLift p ∧ dipoleLift p < b}) ∧
    ∃ N : Set ℝ, volume N = 0 ∧ ∀ a b : ℝ, 0 < a → a < b → b < 2 →
      a ∉ N → b ∉ N →
      (∫ p in {p | p ∈ cellSquare ∧ a < dipoleLift p ∧ dipoleLift p < b},
        ddVirialDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy p) =
      ddVirialLevel (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy a -
        ddVirialLevel (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy b := by
  have iJ (a : ℝ) (ha : 0 < a) := ddVirialDensity_integrable ha
    (ddStreamQuotient_memSobolevOn ω ha).1 (ddVorticityQuotient_memLp ω ha).neg
    (ddStreamQuotient_memLp_derivative hx ha) (ddStreamQuotient_memLp_derivative hy ha)
  have iB (a : ℝ) (ha : 0 < a) := ddBoundaryDensity_integrable ha
    (ddStreamQuotient_memSobolevOn ω ha).1 (ddVorticityQuotient_memLp ω ha).neg
    (ddStreamQuotient_memLp_derivative hx ha) (ddStreamQuotient_memLp_derivative hy ha)
  refine ⟨fun a b ha _ _ ↦ (iJ a ha).mono_set (fun _ hp ↦ ⟨hp.1, hp.2.1⟩), ?_⟩
  obtain ⟨N, hN, hann⟩ := annular_virial_of_cutoff_identity
    (J := ddVirialDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy)
    (B := ddBoundaryDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy)
    (fun a _ ha _ ↦ (iJ a ha).mono_set fun _ hp ↦ ⟨hp.1, by linarith [hp.2.1]⟩)
    (fun a _ ha _ ↦ (iB a ha).mono_set fun _ hp ↦ ⟨hp.1, by linarith [hp.2.1]⟩) hcut
  refine ⟨(fun ε : ℝ ↦ ε / 2) ⁻¹' N, ?_, fun a b ha hab hb haN hbN ↦ ?_⟩
  · rw [show (fun ε : ℝ ↦ ε / 2) = (fun ε ↦ (1 / 2 : ℝ) * ε) by funext ε; ring,
      Real.volume_preimage_mul_left (by norm_num : (1 / 2 : ℝ) ≠ 0), hN, mul_zero]
  · have h := hann (a / 2) (b / 2) (by linarith) (by linarith) (by linarith) haN hbN
    rw [levelIntegral_ddBoundaryDensity _ _ _ _ (by linarith) (by linarith),
      levelIntegral_ddBoundaryDensity _ _ _ _ (by linarith) (by linarith)] at h
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using h

/-- The weak weighted cutoff identity on the original eigenfunction domain.
    Its test is supported on normalized levels in a compact subinterval of (0,1). -/
theorem dd_cutoff_identity {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    {ux uy : ℝ × ℝ → ℂ}
    (hx : HasWeakPartialOn cellSquare 0 (ddStreamQuotient ω) ux)
    (hy : HasWeakPartialOn cellSquare 1 (ddStreamQuotient ω) uy)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1)
    (hsupp : ∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) :
    (∫ p in cellSquare, φ (dipoleLift p / 2) *
      ddVirialDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy p) =
    ∫ p in cellSquare, deriv φ (dipoleLift p / 2) / 2 *
      ddBoundaryDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy p := by
  let χ : ℝ → ℝ := fun s ↦ φ (s / 2)
  have hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ :=
    hφ.comp (contDiff_id.div_const 2)
  have hχ' (s : ℝ) : deriv χ s = deriv φ (s / 2) / 2 := by
    have h := ((hφ.differentiable (by simp)) (s / 2)).hasDerivAt.comp s
      ((hasDerivAt_id s).div_const 2)
    exact h.deriv.trans (by ring)
  have hχcc : tsupport χ ⊆ Icc (2 * a) (2 * b) := by
    apply closure_minimal _ isClosed_Icc
    intro s hs
    obtain ⟨h1, h2⟩ := hsupp (s / 2) hs
    exact ⟨by linarith, by linarith⟩
  have hc : HasCompactSupport χ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport χ) hχcc
  have hχs : tsupport χ ⊆ Ioo (0 : ℝ) 2 := fun s hs ↦
    ⟨by linarith [(hχcc hs).1], by linarith [(hχcc hs).2]⟩
  -- Choose the weak Poisson witnesses, then replace them by the supplied ones.
  obtain ⟨vx, vy, hop⟩ := dd_quotient_equations hω
  have hxeq := hop.1.ae_eq isOpen_cellSquare hx
  have hyeq := hop.2.1.ae_eq isOpen_cellSquare hy
  have hop' : HasDDOperator (ddStreamQuotient ω)
      (fun p ↦ -ddVorticityQuotient ω p) ux uy := by
    refine ⟨hx, hy, hop.2.2.1, fun η hη ↦ ?_⟩
    rw [hop.2.2.2 η hη]
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' isOpen_cellSquare.measurableSet).mpr hxeq,
      (ae_restrict_iff' isOpen_cellSquare.measurableSet).mpr hyeq] with p hpx hpy
    rw [hpx, hpy]
  have he : MemSobolevLocOn 0 cellSquare (fun p ↦ -ddVorticityQuotient ω p) := by
    intro V hV hcV hsub
    exact MemLp.neg ((ddVorticityQuotient_memSobolevLocOn ω) V hV hcV hsub)
  have hg := dd_weak_green (ddStreamQuotient_memSobolevLocOn ω) he hop' hχ hc hχs
  -- The flux identity is used only where χ' is nonzero, hence off the center.
  have hboundary :
      (∫ p in cellSquare, deriv χ (dipoleLift p) *
        (ddGreenNormalFlux (ddStreamQuotient ω) ux uy p -
          ddWeight p * ddVirialQ (dipoleLift p) *
            (-ddVorticityQuotient ω p * (starRingEnd ℂ) (ddStreamQuotient ω p)).re)) =
      ∫ p in cellSquare, deriv χ (dipoleLift p) *
        ddBoundaryDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy p := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem isOpen_cellSquare.measurableSet] with p hp
    by_cases hd : deriv χ (dipoleLift p) = 0
    · simp [hd]
    · have hs := hχs (support_deriv_subset hd)
      rw [dd_boundary_flux (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy
        (show p ∈ ddRegularCell from
          ⟨hp, (gradSq_dipoleLift_pos hs.1 hs.2).ne'⟩)]
  rw [hboundary] at hg
  have hpair (p : ℝ × ℝ) :
      ‖-ddVorticityQuotient ω p‖ ^ 2 -
        (-ddVorticityQuotient ω p * (starRingEnd ℂ) (ddStreamQuotient ω p)).re =
      (ddVorticityQuotient ω p * (starRingEnd ℂ)
        (ddVorticityQuotient ω p + ddStreamQuotient ω p)).re := by
    simp only [norm_neg, map_add, mul_add, Complex.add_re, neg_mul, Complex.neg_re,
      sub_neg_eq_add]
    congr 1
    simp [Complex.mul_conj, Complex.sq_norm]
  simp_rw [hpair] at hg
  simp only [map_neg, mul_neg, Complex.neg_re, integral_neg] at hg
  have hfirst := dd_weighted_first hlam hω hs hx hy hχ hc hχs
  have hid :
      (∫ p in cellSquare, χ (dipoleLift p) *
        ddVirialDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy p) =
      ∫ p in cellSquare, deriv χ (dipoleLift p) *
        ddBoundaryDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy p := by
    linarith
  simpa only [hχ'] using hid

/-- Annular virial with one common exceptional set for both endpoints. Neither a
    derivative of the vorticity nor global quotient data are hypotheses. -/
theorem dd_annular_virial {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    {ux uy : ℝ × ℝ → ℂ}
    (hx : HasWeakPartialOn cellSquare 0 (ddStreamQuotient ω) ux)
    (hy : HasWeakPartialOn cellSquare 1 (ddStreamQuotient ω) uy) :
    (∀ a b : ℝ, 0 < a → a < b → b < 2 →
      IntegrableOn (ddVirialDensity (ddStreamQuotient ω)
        (fun p ↦ -ddVorticityQuotient ω p) ux uy)
        {p | p ∈ cellSquare ∧ a < dipoleLift p ∧ dipoleLift p < b}) ∧
    ∃ N : Set ℝ, volume N = 0 ∧ ∀ a b : ℝ, 0 < a → a < b → b < 2 →
      a ∉ N → b ∉ N →
      (∫ p in {p | p ∈ cellSquare ∧ a < dipoleLift p ∧ dipoleLift p < b},
        ddVirialDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy p) =
      ddVirialLevel (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy a -
        ddVirialLevel (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy b := by
  apply dd_annular_virial_of_cutoff_identity ω hx hy
  intro φ hφ a b ha hb hsupp
  exact dd_cutoff_identity hlam hω hs hx hy hφ ha hb hsupp

/-! ### Center flux and removal -/

/-- A quantitative center bound for arbitrary measurable values and first derivatives.
    It uses only a bounded value and square-integrable orbit energy, not an equation. -/
theorem abs_ddVirialLevel_le {u e ux uy : ℝ × ℝ → ℂ}
    (mu : Measurable u) (me : Measurable e) (mx : Measurable ux) (my : Measurable uy)
    {M h : ℝ} (hM0 : 0 ≤ M) (hh : 1 / 2 < h) (h1 : h < 1)
    (hF : IntegrableOn (fun t ↦ ‖u (dipoleOrbit h t)‖ ^ 2 +
      ‖ux (dipoleOrbit h t)‖ ^ 2 + ‖uy (dipoleOrbit h t)‖ ^ 2 +
      ‖e (dipoleOrbit h t)‖ ^ 2) (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h)))
    (hM : ∀ᵐ t ∂(volume.restrict (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h))),
      ‖u (dipoleOrbit h t)‖ ≤ M) :
    |ddVirialLevel u e ux uy (2 * h)| ≤
      4 * M * √(128 * ((1 - h) * ∫ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
        (‖u (dipoleOrbit h t)‖ ^ 2 + ‖ux (dipoleOrbit h t)‖ ^ 2 +
          ‖uy (dipoleOrbit h t)‖ ^ 2 + ‖e (dipoleOrbit h t)‖ ^ 2))) +
      96 * ((1 - h) * ∫ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
        (‖u (dipoleOrbit h t)‖ ^ 2 + ‖ux (dipoleOrbit h t)‖ ^ 2 +
          ‖uy (dipoleOrbit h t)‖ ^ 2 + ‖e (dipoleOrbit h t)‖ ^ 2)) := by
  have h0 : 0 < h := by linarith
  have hL := eighthPeriod_pos h0 h1
  have hL2 : eighthPeriod h ≤ 2 :=
    (eighthPeriod_le_inv h0 h1).trans (by rw [div_le_iff₀ h0]; linarith)
  let I := Ico (-2 * eighthPeriod h) (6 * eighthPeriod h)
  let γ := fun t ↦ dipoleOrbit h t
  let n := ddInwardNormal ux uy
  let τ := tangentDeriv ux uy
  let F := fun t ↦ ‖u (γ t)‖ ^ 2 + ‖ux (γ t)‖ ^ 2 +
    ‖uy (γ t)‖ ^ 2 + ‖e (γ t)‖ ^ 2
  let B := fun t ↦ ‖n (γ t)‖ ^ 2 - ‖τ (γ t)‖ ^ 2 - ‖u (γ t)‖ ^ 2 +
    (e (γ t) * (starRingEnd ℂ) (u (γ t))).re
  let A := fun t ↦ gradNorm (γ t) * ((starRingEnd ℂ) (u (γ t)) * n (γ t)).re
  have mγ : Measurable γ :=
    (continuous_dipoleOrbit.comp (continuous_const.prodMk continuous_id)).measurable
  have mn : Measurable (fun t ↦ n (γ t)) := by
    dsimp [n, ddInwardNormal, normalDeriv, gradNorm]
    fun_prop
  have mt : Measurable (fun t ↦ τ (γ t)) := by
    dsimp [τ, tangentDeriv, gradNorm]
    fun_prop
  have mρ : Measurable (fun t ↦ gradNorm (γ t)) := by unfold gradNorm; fun_prop
  have hρ0 (t) : 0 ≤ gradNorm (γ t) := Real.sqrt_nonneg _
  have hρ2 (t) : gradNorm (γ t) ^ 2 ≤ 4 * (1 - h) := by
    have hΨ := dipoleLift_dipoleOrbit h0 h1 t
    change dipoleLift (γ t) = 2 * h at hΨ
    rw [gradNorm, Real.sq_sqrt (by positivity)]
    simp only [dipoleLift] at hΨ
    nlinarith [Real.sin_sq_add_cos_sq (γ t).1, Real.sin_sq_add_cos_sq (γ t).2,
      sq_nonneg (1 - Real.cos (γ t).1), sq_nonneg (1 - Real.cos (γ t).2)]
  have hn (t) : ‖n (γ t)‖ ^ 2 ≤ 2 * F t := by
    have hb := norm_normalDeriv_le ux uy (γ t)
    have he : ‖n (γ t)‖ = ‖normalDeriv ux uy (γ t)‖ := norm_neg _
    rw [← he] at hb
    dsimp only [F]
    nlinarith [norm_nonneg (n (γ t)), norm_nonneg (ux (γ t)), norm_nonneg (uy (γ t)),
      sq_nonneg (‖ux (γ t)‖ - ‖uy (γ t)‖), sq_nonneg (‖u (γ t)‖), sq_nonneg (‖e (γ t)‖)]
  have ht (t) : ‖τ (γ t)‖ ^ 2 ≤ 2 * F t := by
    have hb := norm_tangentDeriv_le ux uy (γ t)
    dsimp only [F]
    nlinarith [norm_nonneg (τ (γ t)), norm_nonneg (ux (γ t)), norm_nonneg (uy (γ t)),
      sq_nonneg (‖ux (γ t)‖ - ‖uy (γ t)‖), sq_nonneg (‖u (γ t)‖), sq_nonneg (‖e (γ t)‖)]
  have hu (t) : ‖u (γ t)‖ ^ 2 ≤ F t := by
    dsimp only [F]
    nlinarith [sq_nonneg (‖ux (γ t)‖), sq_nonneg (‖uy (γ t)‖), sq_nonneg (‖e (γ t)‖)]
  have hre (a b : ℂ) : |(a * (starRingEnd ℂ) b).re| ≤ ‖a‖ * ‖b‖ :=
    (Complex.abs_re_le_norm _).trans (by rw [norm_mul, Complex.norm_conj])
  have hp (t) : |(e (γ t) * (starRingEnd ℂ) (u (γ t))).re| ≤ F t := by
    refine (hre _ _).trans ?_
    dsimp only [F]
    nlinarith [sq_nonneg (‖e (γ t)‖ - ‖u (γ t)‖),
      sq_nonneg (‖ux (γ t)‖), sq_nonneg (‖uy (γ t)‖)]
  have hb (t) : |B t| ≤ 6 * F t := by
    have hp' := abs_le.mp (hp t)
    dsimp only [B]
    apply abs_le.mpr
    constructor <;> nlinarith [hn t, ht t, hu t,
      sq_nonneg (‖n (γ t)‖), sq_nonneg (‖τ (γ t)‖), sq_nonneg (‖u (γ t)‖)]
  have ha (t) : |A t| ≤ 3 * F t := by
    dsimp only [A]
    rw [abs_mul, abs_of_nonneg (hρ0 t)]
    have hr : gradNorm (γ t) ≤ 2 := by nlinarith [hρ2 t, hρ0 t]
    have hrp : |((starRingEnd ℂ) (u (γ t)) * n (γ t)).re| ≤ ‖u (γ t)‖ * ‖n (γ t)‖ := by
      simpa [mul_comm] using hre (n (γ t)) (u (γ t))
    nlinarith [mul_le_mul hr hrp (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
      hn t, hu t, sq_nonneg (‖u (γ t)‖ - ‖n (γ t)‖)]
  have iF : Integrable F (volume.restrict I) := hF
  have iN : Integrable (fun t ↦ ‖n (γ t)‖ ^ 2) (volume.restrict I) :=
    (iF.const_mul 2).mono' (mn.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hn t)
  have iB : Integrable B (volume.restrict I) :=
    (iF.const_mul 6).mono'
      (((mn.norm.pow_const 2).sub (mt.norm.pow_const 2)).sub
        ((mu.comp mγ).norm.pow_const 2) |>.add
        (Complex.measurable_re.comp ((me.comp mγ).mul
          (Complex.continuous_conj.measurable.comp (mu.comp mγ))))).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ hb t)
  have iA : Integrable A (volume.restrict I) :=
    (iF.const_mul 3).mono'
      (mρ.mul (Complex.measurable_re.comp
        ((Complex.continuous_conj.measurable.comp (mu.comp mγ)).mul mn))).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ ha t)
  have iρ : Integrable (fun t ↦ gradNorm (γ t) ^ 2) (volume.restrict I) :=
    (integrable_const (4 * (1 - h))).mono' (mρ.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hρ2 t)
  have iρn : Integrable (fun t ↦ gradNorm (γ t) * ‖n (γ t)‖) (volume.restrict I) :=
    (iρ.add iN).mono' (mρ.mul mn.norm).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by
        rw [Real.norm_of_nonneg (mul_nonneg (hρ0 t) (norm_nonneg _)), Pi.add_apply]
        nlinarith [sq_nonneg (gradNorm (γ t) - ‖n (γ t)‖)])
  let g := ∫ t in I, F t
  have hg0 : 0 ≤ g := integral_nonneg fun t ↦ by dsimp only [F]; positivity
  have hNI : (∫ t in I, ‖n (γ t)‖ ^ 2) ≤ 2 * g := by
    rw [← integral_const_mul]
    exact integral_mono iN (iF.const_mul 2) hn
  have hBI : |∫ t in I, B t| ≤ 6 * g := by
    rw [← integral_const_mul]
    exact abs_integral_le_integral_abs.trans (integral_mono iB.abs (iF.const_mul 6) hb)
  have hρI : ∫ t in I, gradNorm (γ t) ^ 2 ≤ 64 * (1 - h) := by
    calc _ ≤ ∫ t in I, 4 * (1 - h) := integral_mono iρ (integrable_const _) hρ2
      _ = 8 * eighthPeriod h * (4 * (1 - h)) := by
        rw [setIntegral_const, Real.volume_real_Ico_of_le (by linarith),
          smul_eq_mul]
        ring
      _ ≤ _ := by nlinarith
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict I)
    Real.HolderConjugate.two_two (Eventually.of_forall hρ0)
    (Eventually.of_forall fun t ↦ norm_nonneg (n (γ t)))
    (by rw [ENNReal.ofReal_ofNat]
        exact (memLp_two_iff_integrable_sq mρ.aestronglyMeasurable).2 iρ)
    (by rw [ENNReal.ofReal_ofNat]
        exact (memLp_two_iff_integrable_sq mn.norm.aestronglyMeasurable).2 iN)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hCS
  have hAI : |∫ t in I, A t| ≤ M * √(128 * ((1 - h) * g)) := by
    calc _ ≤ ∫ t in I, |A t| := abs_integral_le_integral_abs
      _ ≤ ∫ t in I, M * (gradNorm (γ t) * ‖n (γ t)‖) := by
        apply integral_mono_ae iA.abs (iρn.const_mul M)
        filter_upwards [hM] with t hMt
        dsimp only [A]
        rw [abs_mul, abs_of_nonneg (hρ0 t)]
        have hrp : |((starRingEnd ℂ) (u (γ t)) * n (γ t)).re| ≤
            ‖u (γ t)‖ * ‖n (γ t)‖ := by
          simpa [mul_comm] using hre (n (γ t)) (u (γ t))
        calc _ ≤ gradNorm (γ t) * (‖u (γ t)‖ * ‖n (γ t)‖) :=
            mul_le_mul_of_nonneg_left hrp (hρ0 t)
          _ ≤ gradNorm (γ t) * (M * ‖n (γ t)‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hMt (norm_nonneg _)) (hρ0 t)
          _ = _ := by ring
      _ = M * ∫ t in I, gradNorm (γ t) * ‖n (γ t)‖ := integral_const_mul _ _
      _ ≤ M * (√(∫ t in I, gradNorm (γ t) ^ 2) *
          √(∫ t in I, ‖n (γ t)‖ ^ 2)) := by gcongr
      _ ≤ M * (√(64 * (1 - h)) * √(2 * g)) := by gcongr
      _ = _ := by
        rw [← Real.sqrt_mul (by linarith)]
        congr 2
        ring
  have hc0 : 0 ≤ (8 - (2 * h) ^ 3) / 3 := by
    have hp := pow_le_pow_left₀ h0.le h1.le 3
    norm_num at hp
    nlinarith
  have hc : (8 - (2 * h) ^ 3) / 3 ≤ 16 * (1 - h) := by
    have h2 : h ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - h) (by nlinarith : 0 ≤ 5 - h - h ^ 2)]
  have hG : ddVirialLevel u e ux uy (2 * h) =
      (8 - (2 * h) ^ 3) / 3 * (∫ t in I, B t) - (2 * h) ^ 2 * ∫ t in I, A t := by
    unfold ddVirialLevel
    rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
      levelIntegral_eq_integral_orbitWindow h0 h1]
    simp_rw [mul_assoc ((2 * h) ^ 2)]
    exact (integral_sub (iB.const_mul _) (iA.const_mul _)).trans
      (by rw [integral_const_mul, integral_const_mul])
  rw [hG]
  calc _ ≤ (8 - (2 * h) ^ 3) / 3 * |∫ t in I, B t| +
        (2 * h) ^ 2 * |∫ t in I, A t| := by
          have hb := abs_sub ((8 - (2 * h) ^ 3) / 3 * ∫ t in I, B t)
            ((2 * h) ^ 2 * ∫ t in I, A t)
          rw [abs_mul, abs_mul, abs_of_nonneg hc0,
            abs_of_nonneg (sq_nonneg (2 * h))] at hb
          exact hb
    _ ≤ 16 * (1 - h) * (6 * g) + 4 * (M * √(128 * ((1 - h) * g))) := by
      gcongr
      nlinarith
    _ = _ := by ring

/-- The weighted boundary term vanishes along center levels avoiding any prescribed
    null set. Energy is required only on the fixed inner truncation `Ψ > 1`. -/
theorem dd_center_limit {u e ux uy : ℝ × ℝ → ℂ}
    (mu : Measurable u) (me : Measurable e) (mx : Measurable ux) (my : Measurable uy)
    (hi : IntegrableOn (fun p ↦ ‖u p‖ ^ 2 + ‖ux p‖ ^ 2 + ‖uy p‖ ^ 2 + ‖e p‖ ^ 2)
      (ddTruncatedCell 1))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ p ∈ ddTruncatedCell 1, ‖u p‖ ≤ M)
    {N : Set ℝ} (hN : volume N = 0) :
    ∃ seq : ℕ → ℝ, (∀ j, seq j ∈ Ioo 0 1 ∧ seq j ∉ N) ∧
      Tendsto seq atTop (𝓝 1) ∧
      Tendsto (fun j ↦ ddVirialLevel u e ux uy (2 * seq j)) atTop (𝓝 0) := by
  let F := (ddTruncatedCell 1).indicator
    (fun p ↦ ‖u p‖ ^ 2 + ‖ux p‖ ^ 2 + ‖uy p‖ ^ 2 + ‖e p‖ ^ 2)
  have mF : Measurable F := by
    apply Measurable.indicator _ (isOpen_ddTruncatedCell 1).measurableSet
    fun_prop
  have iF : IntegrableOn F cellSquare :=
    hi.integrable_indicator (isOpen_ddTruncatedCell 1).measurableSet |>.integrableOn
  have hF0 (p) : 0 ≤ F p := by
    apply Set.indicator_nonneg
    intro p _
    positivity
  have hg : ∫⁻ h in Ioo 0 1, ∫⁻ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
      ENNReal.ofReal (F (dipoleOrbit h t)) ≠ ⊤ := by
    intro htop
    have hc := lintegral_cellSquare_eq (ENNReal.measurable_ofReal.comp mF)
    have hlt := iF.lintegral_lt_top
    simp only [Function.comp_apply] at hc
    rw [hc, htop, ENNReal.mul_top (by norm_num)] at hlt
    exact lt_irrefl _ hlt
  have hgood : ∀ᵐ h ∂(volume.restrict (Ioo 0 1)), 1 / 2 < h → h < 1 →
      |ddVirialLevel u e ux uy (2 * h)| ≤
        4 * M * √(128 * ((1 - h) * (∫⁻ t in Ico (-2 * eighthPeriod h)
          (6 * eighthPeriod h), ENNReal.ofReal (F (dipoleOrbit h t))).toReal)) +
        96 * ((1 - h) * (∫⁻ t in Ico (-2 * eighthPeriod h)
          (6 * eighthPeriod h), ENNReal.ofReal (F (dipoleOrbit h t))).toReal) := by
    filter_upwards [(integral_cellSquare_eq iF).1] with h hFh hh h1
    have horbit (t) : dipoleOrbit h t ∈ ddTruncatedCell 1 :=
      ⟨dipoleOrbit_mem_cellSquare (by linarith) h1 t,
        by rw [dipoleLift_dipoleOrbit (by linarith) h1]; linarith⟩
    have hFeq (t) : F (dipoleOrbit h t) =
        ‖u (dipoleOrbit h t)‖ ^ 2 + ‖ux (dipoleOrbit h t)‖ ^ 2 +
          ‖uy (dipoleOrbit h t)‖ ^ 2 + ‖e (dipoleOrbit h t)‖ ^ 2 :=
      indicator_of_mem (horbit t) _
    have hb := abs_ddVirialLevel_le mu me mx my hM0 hh h1
      (hFh.congr_fun (fun t _ ↦ hFeq t) measurableSet_Ico)
      (ae_restrict_of_forall_mem measurableSet_Ico (fun t _ ↦ hM _ (horbit t)))
    have hint : (∫ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h), F (dipoleOrbit h t)) =
        (∫⁻ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
          ENNReal.ofReal (F (dipoleOrbit h t))).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun t ↦ hF0 _)
        hFh.aestronglyMeasurable
    rw [← hint]
    simpa only [hFeq] using hb
  rw [ae_restrict_iff' measurableSet_Ioo] at hgood
  obtain ⟨seq, hmem, hlim, hprod⟩ := exists_seq_one_sub_mul_tendsto_zero hg
    (N := N ∪ {h | ¬(h ∈ Ioo 0 1 → 1 / 2 < h → h < 1 → _)})
    (measure_union_null hN (ae_iff.1 hgood))
  refine ⟨seq, fun j ↦ ⟨(hmem j).1, fun h ↦ (hmem j).2 (Or.inl h)⟩, hlim, ?_⟩
  have hpr : Tendsto (fun j ↦ (1 - seq j) * (∫⁻ t in Ico (-2 * eighthPeriod (seq j))
      (6 * eighthPeriod (seq j)), ENNReal.ofReal (F (dipoleOrbit (seq j) t))).toReal)
      atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hprod
    simp only [ENNReal.toReal_zero] at h
    exact h.congr fun j ↦ by
      simp only [Function.comp_apply, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by linarith [(hmem j).1.2] : 0 ≤ 1 - seq j)]
  have hup : Tendsto (fun j ↦
      4 * M * √(128 * ((1 - seq j) * (∫⁻ t in Ico (-2 * eighthPeriod (seq j))
        (6 * eighthPeriod (seq j)), ENNReal.ofReal (F (dipoleOrbit (seq j) t))).toReal)) +
      96 * ((1 - seq j) * (∫⁻ t in Ico (-2 * eighthPeriod (seq j))
        (6 * eighthPeriod (seq j)), ENNReal.ofReal (F (dipoleOrbit (seq j) t))).toReal))
      atTop (𝓝 0) := by
    simpa using ((hpr.const_mul 128).sqrt.const_mul (4 * M)).add (hpr.const_mul 96)
  refine squeeze_zero_norm' ?_ hup
  filter_upwards [hlim.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))]
    with j hj
  have hgj := (hmem j).2
  simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hgj
  exact hgj.2 (hmem j).1 hj (hmem j).1.2

/-- Coarea transfers even nonmeasurable a.e. properties: cover the bad planar set
    by a measurable null set before applying the measurable coarea interface. -/
theorem ae_level_of_ae_cellSquare' {P : ℝ × ℝ → Prop}
    (hP : ∀ᵐ p ∂(volume.restrict cellSquare), P p) :
    ∀ᵐ h ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ∀ᵐ t ∂(volume.restrict (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h))),
        P (dipoleOrbit h t) := by
  have hc : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  let B := {p | p ∈ cellSquare ∧ ¬P p}
  have hB : volume B = 0 := by
    simpa only [ae_iff, not_imp] using (ae_restrict_iff' hc).mp hP
  let M := toMeasurable volume B
  have hM : volume M = 0 := by rw [measure_toMeasurable, hB]
  have hlevels := ae_level_of_ae_cellSquare
    (measurableSet_toMeasurable volume B).compl
    (ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hM))
  filter_upwards [hlevels, ae_restrict_mem measurableSet_Ioo] with h hh hi
  filter_upwards [hh] with t ht
  by_contra hbad
  exact ht (subset_toMeasurable volume B
    ⟨dipoleOrbit_mem_cellSquare hi.1 hi.2 t, hbad⟩)

/-- Center removal for the original eigenfunction quotients and arbitrary weak
    derivative witnesses; no global divided-domain theorem is invoked. -/
theorem dd_raw_center_limit (ω : L2) {ux uy : ℝ × ℝ → ℂ}
    (hx : HasWeakPartialOn cellSquare 0 (ddStreamQuotient ω) ux)
    (hy : HasWeakPartialOn cellSquare 1 (ddStreamQuotient ω) uy)
    {N : Set ℝ} (hN : volume N = 0) :
    ∃ seq : ℕ → ℝ, (∀ j, seq j ∈ Ioo 0 2 ∧ seq j ∉ N) ∧
      Tendsto seq atTop (𝓝 2) ∧
      Tendsto (fun j ↦ ddVirialLevel (ddStreamQuotient ω)
        (fun p ↦ -ddVorticityQuotient ω p) ux uy (seq j)) atTop (𝓝 0) := by
  have hxl := ddStreamQuotient_memLp_derivative hx (by norm_num : (0 : ℝ) < 1)
  have hyl := ddStreamQuotient_memLp_derivative hy (by norm_num : (0 : ℝ) < 1)
  let X := hxl.aestronglyMeasurable.mk ux
  let Y := hyl.aestronglyMeasurable.mk uy
  have mX : Measurable X := hxl.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have mY : Measurable Y := hyl.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hX : ux =ᵐ[volume.restrict (ddTruncatedCell 1)] X := hxl.aestronglyMeasurable.ae_eq_mk
  have hY : uy =ᵐ[volume.restrict (ddTruncatedCell 1)] Y := hyl.aestronglyMeasurable.ae_eq_mk
  have iU : IntegrableOn (fun p ↦ ‖ddStreamQuotient ω p‖ ^ 2) (ddTruncatedCell 1) :=
    (memLp_two_iff_integrable_sq
      (measurable_ddStreamQuotient ω).norm.aestronglyMeasurable).mp
      (ddStreamQuotient_memSobolevOn ω (by norm_num : (0 : ℝ) < 1)).1.norm
  have iE : IntegrableOn (fun p ↦ ‖-ddVorticityQuotient ω p‖ ^ 2) (ddTruncatedCell 1) :=
    (memLp_two_iff_integrable_sq
      (measurable_ddVorticityQuotient ω).neg.norm.aestronglyMeasurable).mp
      (ddVorticityQuotient_memLp ω (by norm_num : (0 : ℝ) < 1)).neg.norm
  have iX : IntegrableOn (fun p ↦ ‖X p‖ ^ 2) (ddTruncatedCell 1) :=
    (memLp_two_iff_integrable_sq mX.norm.aestronglyMeasurable).mp
      ((memLp_congr_ae hX).mp hxl).norm
  have iY : IntegrableOn (fun p ↦ ‖Y p‖ ^ 2) (ddTruncatedCell 1) :=
    (memLp_two_iff_integrable_sq mY.norm.aestronglyMeasurable).mp
      ((memLp_congr_ae hY).mp hyl).norm
  have hbound (p) (hp : p ∈ ddTruncatedCell 1) :
      ‖ddStreamQuotient ω p‖ ≤ ‖continuousRep (invLap ω)‖ := by
    have hs : 0 < dipoleLift p := lt_trans (by norm_num) hp.2
    rw [ddStreamQuotient, norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le]
    calc _ ≤ ‖contStream ω p‖ := div_le_self (norm_nonneg _) hp.2.le
      _ ≤ _ := (continuousRep (invLap ω)).norm_coe_le_norm _
  have hrep : ∀ᵐ p ∂(volume.restrict cellSquare),
      p ∈ ddTruncatedCell 1 → ux p = X p ∧ uy p = Y p := by
    filter_upwards [ae_restrict_of_ae
      ((ae_restrict_iff' (isOpen_ddTruncatedCell 1).measurableSet).mp hX),
      ae_restrict_of_ae
        ((ae_restrict_iff' (isOpen_ddTruncatedCell 1).measurableSet).mp hY)]
      with p hp hq hpc
    exact ⟨hp hpc, hq hpc⟩
  let P : ℝ → Prop := fun h ↦ 1 / 2 < h →
    ddVirialLevel (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy (2 * h) =
      ddVirialLevel (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) X Y (2 * h)
  have hP : ∀ᵐ h ∂(volume.restrict (Ioo (0 : ℝ) 1)), P h := by
    filter_upwards [ae_level_of_ae_cellSquare' hrep, ae_restrict_mem measurableSet_Ioo]
      with h hh hi hhalf
    unfold ddVirialLevel
    rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
      levelIntegral_eq_integral_orbitWindow hi.1 hi.2,
      levelIntegral_eq_integral_orbitWindow hi.1 hi.2]
    apply integral_congr_ae
    filter_upwards [hh] with t ht
    have hp : dipoleOrbit h t ∈ ddTruncatedCell 1 :=
      ⟨dipoleOrbit_mem_cellSquare hi.1 hi.2 t,
        by rw [dipoleLift_dipoleOrbit hi.1 hi.2]; linarith⟩
    obtain ⟨hx, hy⟩ := ht hp
    simp only [ddInwardNormal, normalDeriv, tangentDeriv, hx, hy]
  let B := {h | h ∈ Ioo 0 1 ∧ ¬P h}
  have hB : volume B = 0 := by
    simpa only [ae_iff, not_imp] using (ae_restrict_iff' measurableSet_Ioo).mp hP
  have hNr : volume ((fun h : ℝ ↦ 2 * h) ⁻¹' N) = 0 := by
    rw [Real.volume_preimage_mul_left (by norm_num : (2 : ℝ) ≠ 0), hN, mul_zero]
  obtain ⟨seq, hseq, hlim, hG⟩ := dd_center_limit
    (measurable_ddStreamQuotient ω) (measurable_ddVorticityQuotient ω).neg mX mY
    (((iU.add iX).add iY).add iE) (norm_nonneg _) hbound
    (measure_union_null hNr hB)
  refine ⟨fun j ↦ 2 * seq j, fun j ↦ ⟨⟨by linarith [(hseq j).1.1],
    by linarith [(hseq j).1.2]⟩, fun hj ↦ (hseq j).2 (Or.inl hj)⟩, ?_, ?_⟩
  · simpa using hlim.const_mul (2 : ℝ)
  · apply hG.congr'
    filter_upwards [hlim.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))]
      with j hj
    have hp : P (seq j) := by
      by_contra hbad
      exact (hseq j).2 (Or.inr ⟨(hseq j).1, hbad⟩)
    exact (hp hj).symm

/-- Truncated virial including the center, at almost every positive stream level. -/
theorem dd_truncated_virial {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    {ux uy : ℝ × ℝ → ℂ}
    (hx : HasWeakPartialOn cellSquare 0 (ddStreamQuotient ω) ux)
    (hy : HasWeakPartialOn cellSquare 1 (ddStreamQuotient ω) uy) :
    ∀ᵐ ε ∂(volume.restrict (Ioo (0 : ℝ) 2)),
      IntegrableOn (ddVirialDensity (ddStreamQuotient ω)
        (fun p ↦ -ddVorticityQuotient ω p) ux uy) (ddTruncatedCell ε) ∧
      (∫ p in ddTruncatedCell ε,
        ddVirialDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy p) =
      ddVirialLevel (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy ε := by
  obtain ⟨-, N, hN, hann⟩ := dd_annular_virial hlam hω hs hx hy
  have hlt2 : ∀ᵐ p : ℝ × ℝ, dipoleLift p < 2 := by
    filter_upwards [ae_cos_fst_ne_cos_snd] with p hp
    by_contra hge
    exact hp (by
      have h1 := Real.cos_le_one p.1
      have h2 := Real.cos_le_one p.2
      unfold dipoleLift at hge
      linarith)
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hN)] with a ha haN
  have hi := ddVirialDensity_integrable ha.1
    (ddStreamQuotient_memSobolevOn ω ha.1).1
    (ddVorticityQuotient_memLp ω ha.1).neg
    (ddStreamQuotient_memLp_derivative hx ha.1)
    (ddStreamQuotient_memLp_derivative hy ha.1)
  refine ⟨hi, ?_⟩
  obtain ⟨seq, hseq, hlim, hG⟩ := dd_raw_center_limit ω hx hy hN
  let D := ddVirialDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p) ux uy
  let A := ddTruncatedCell a
  have hm (b : ℝ) : MeasurableSet {p | dipoleLift p < b} :=
    measurableSet_lt (show Measurable dipoleLift by unfold dipoleLift; fun_prop) measurable_const
  have hset (j : ℕ) : {p | p ∈ cellSquare ∧ a < dipoleLift p ∧ dipoleLift p < seq j} =
      A ∩ {p | dipoleLift p < seq j} := by
    ext p
    simp only [A, ddTruncatedCell, mem_ofPred_eq, mem_inter_iff, and_assoc]
  have hev : ∀ᶠ j in atTop, a < seq j := hlim.eventually (lt_mem_nhds ha.2)
  have hlim1 : Tendsto (fun j ↦ ∫ p in A ∩ {p | dipoleLift p < seq j}, D p)
      atTop (𝓝 (ddVirialLevel (ddStreamQuotient ω)
        (fun p ↦ -ddVorticityQuotient ω p) ux uy a)) := by
    have hd := (tendsto_const_nhds (x := ddVirialLevel (ddStreamQuotient ω)
      (fun p ↦ -ddVorticityQuotient ω p) ux uy a)).sub hG
    rw [sub_zero] at hd
    apply hd.congr'
    filter_upwards [hev] with j hj
    rw [← hset]
    exact (hann a (seq j) ha.1 hj (hseq j).1.2 haN (hseq j).2).symm
  have hlim2 : Tendsto (fun j ↦ ∫ p in A ∩ {p | dipoleLift p < seq j}, D p)
      atTop (𝓝 (∫ p in A, D p)) := by
    have hind (j : ℕ) : (∫ p in A ∩ {p | dipoleLift p < seq j}, D p) =
        ∫ p in A, {p | dipoleLift p < seq j}.indicator D p := by
      rw [Set.inter_comm A, ← Measure.restrict_restrict (hm _), integral_indicator (hm _)]
    simp_rw [hind]
    apply tendsto_integral_of_dominated_convergence (fun p ↦ ‖D p‖)
    · exact fun j ↦ hi.aestronglyMeasurable.indicator (hm _)
    · exact hi.norm
    · intro j
      filter_upwards with p
      by_cases hp : p ∈ {p | dipoleLift p < seq j}
      · simp [indicator_of_mem hp]
      · simp [indicator_of_notMem hp]
    · filter_upwards [ae_restrict_of_ae hlt2] with p hp
      apply tendsto_const_nhds.congr'
      filter_upwards [hlim.eventually (lt_mem_nhds hp)] with j hj
      exact (indicator_of_mem (show p ∈ {q | dipoleLift q < seq j} from hj) D).symm
  exact tendsto_nhds_unique hlim2 hlim1

/-- Even H² gradient limits, using specified Fourier derivatives and continuous values.
    All three limits share one exceptional null set in the `ε = Ψ` variable. -/
theorem dd_quotient_gradient_traces {u dx dy : L2} (hu : MemSobolev 2 u)
    (hs : InSector true true u) (hx : HasFourierPartial 0 u dx)
    (hy : HasFourierPartial 1 u dy) :
    (∀ k : Fin 4, Integrable (fun t ↦ Real.cosh t ^ 2 / 2 *
      ‖deriv (ddArcTrace u k) t‖ ^ 2)) ∧
    ∃ N : Set ℝ, volume N = 0 ∧
      Tendsto (fun ε ↦ levelIntegral (ε / 2) (fun p ↦
        ‖ddInwardNormal (liftL2 dx) (liftL2 dy) p‖ ^ 2))
        (𝓝[Ioi 0 \ N] 0) (𝓝 0) ∧
      Tendsto (fun ε ↦ levelIntegral (ε / 2) (fun p ↦
        ‖tangentDeriv (liftL2 dx) (liftL2 dy) p‖ ^ 2))
        (𝓝[Ioi 0 \ N] 0) (𝓝 (∑ k : Fin 4,
          ∫ t, Real.cosh t ^ 2 / 2 * ‖deriv (ddArcTrace u k) t‖ ^ 2)) ∧
      Tendsto (fun ε ↦ levelIntegral (ε / 2) (fun p ↦ gradNorm p *
        ((starRingEnd ℂ) (continuousRep u (torusProj p)) *
          ddInwardNormal (liftL2 dx) (liftL2 dy) p).re))
        (𝓝[Ioi 0 \ N] 0) (𝓝 0) := by
  sorry

/-- Change the raw local quotients to supplied data in the truncated virial. The
    conclusion is in the orbit parameter, so the stream level is explicitly `2*h`. -/
theorem DDQuotientData.ae_truncated_virial {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (q : DDQuotientData lam ω) (hω : IsEigenSolution lam ω)
    (hs : InSector false false ω) {dx dy : L2}
    (hx : HasFourierPartial 0 q.phi dx) (hy : HasFourierPartial 1 q.phi dy) :
    ∀ᵐ h ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ddRawBulk q.phi q.nu dx dy (2 * h) =
        ddVirialLevel (fun p ↦ continuousRep q.phi (torusProj p))
          (fun p ↦ -liftL2 q.nu p) (liftL2 dx) (liftL2 dy) (2 * h) := by
  have hm : MeasurableSet cellSquare := by unfold cellSquare diagCoord; measurability
  have hrep := ae_torusProj (coeFn_eq_continuousRep q.regular)
  have hu : ∀ᵐ p, p ∈ cellSquare →
      liftL2 q.phi p = ddStreamQuotient ω p := by
    filter_upwards [hrep] with p hp hpc
    exact hp.trans (q.raw_stream_eq hpc).symm
  have hd (j : Fin 2) (d : L2) (hd : HasFourierPartial j q.phi d) :
      HasWeakPartialOn cellSquare j (ddStreamQuotient ω) (liftL2 d) :=
    (hasWeakPartialOn_liftL2 hd cellSquare).congr_ae_on hm hu
      (Eventually.of_forall fun _ _ ↦ rfl)
  have hv := dd_truncated_virial hlam hω hs (hd 0 dx hx) (hd 1 dy hy)
  have hv' := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (by norm_num : (2 : ℝ) ≠ 0)).ae ((ae_restrict_iff' measurableSet_Ioo).mp hv)
  simp only [smul_eq_mul] at hv'
  have mν : Measurable (liftL2 q.nu) := (Lp.stronglyMeasurable q.nu).measurable.comp
    isOpenQuotientMap_torusProj.continuous.measurable
  have mv : Measurable (ddVorticityQuotient ω) := by
    unfold ddVorticityQuotient dipoleLift liftL2
    have := (Lp.stronglyMeasurable ω).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable
    fun_prop
  have hlevels := ae_level_of_ae_cellSquare (measurableSet_eq_fun mv mν) q.raw_vorticity_eq
  filter_upwards [ae_restrict_of_ae hv', hlevels, ae_restrict_mem measurableSet_Ioo]
    with h hvh hlevel hh
  have hε : 2 * h ∈ Ioo (0 : ℝ) 2 := ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hvir := (hvh hε).2
  have hb : ddRawBulk q.phi q.nu dx dy (2 * h) =
      ∫ p in ddTruncatedCell (2 * h),
        ddVirialDensity (ddStreamQuotient ω) (fun p ↦ -ddVorticityQuotient ω p)
          (liftL2 dx) (liftL2 dy) p := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hrep,
      ae_restrict_of_ae ((ae_restrict_iff' hm).mp q.raw_vorticity_eq),
      ae_restrict_mem (show MeasurableSet (ddTruncatedCell (2 * h)) from
        hm.inter (measurableSet_lt measurable_const
          (show Measurable dipoleLift by unfold dipoleLift; fun_prop)))]
      with p hp hvp hpc
    rw [ddVirialDensity, q.raw_stream_eq hpc.1, hvp hpc.1, norm_neg, ← hp]
    dsimp only [ddVorticityDensity, ddRawEnergy, liftL2]
    ring
  rw [hb, hvir, ddVirialLevel, ddVirialLevel]
  simp only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [levelIntegral_eq_integral_orbitWindow hh.1 hh.2,
    levelIntegral_eq_integral_orbitWindow hh.1 hh.2]
  apply integral_congr_ae
  filter_upwards [hlevel] with t ht
  rw [q.raw_stream_eq (dipoleOrbit_mem_cellSquare hh.1 hh.2 t), ht]

/-- Splitting the boundary integral is justified on almost every level by coarea
    applied separately to the five integrable densities. -/
theorem dd_virial_level_split {φ : L2} (hφ : MemSobolev 2 φ) (ν dx dy : L2) :
    ∀ᵐ h ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      ddVirialLevel (fun p ↦ continuousRep φ (torusProj p))
        (fun p ↦ -liftL2 ν p) (liftL2 dx) (liftL2 dy) (2 * h) =
      (8 - (2 * h) ^ 3) / 3 *
        (levelIntegral h (fun p ↦ ‖ddInwardNormal (liftL2 dx) (liftL2 dy) p‖ ^ 2) -
          levelIntegral h (fun p ↦ ‖tangentDeriv (liftL2 dx) (liftL2 dy) p‖ ^ 2) -
          ddLevelMass φ (2 * h) -
          levelIntegral h (fun p ↦
            (liftL2 ν p * (starRingEnd ℂ) (continuousRep φ (torusProj p))).re)) -
        (2 * h) ^ 2 * levelIntegral h (fun p ↦ gradNorm p *
          ((starRingEnd ℂ) (continuousRep φ (torusProj p)) *
            ddInwardNormal (liftL2 dx) (liftL2 dy) p).re) := by
  let u := fun p ↦ continuousRep φ (torusProj p)
  let n := ddInwardNormal (liftL2 dx) (liftL2 dy)
  let τ := tangentDeriv (liftL2 dx) (liftL2 dy)
  have ml (g : L2) : Measurable (liftL2 g) :=
    (Lp.stronglyMeasurable g).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable
  have mu : Measurable u := ((continuousRep φ).continuous.comp
    isOpenQuotientMap_torusProj.continuous).measurable
  have mn : Measurable n := by
    change Measurable (fun p ↦ -normalDeriv (liftL2 dx) (liftL2 dy) p)
    simp only [normalDeriv, gradNorm]
    fun_prop
  have mt : Measurable τ := by
    change Measurable (fun p ↦ tangentDeriv (liftL2 dx) (liftL2 dy) p)
    simp only [tangentDeriv, gradNorm]
    fun_prop
  have mr : Measurable gradNorm := by unfold gradNorm; fun_prop
  have hsub : cellSquare ⊆
      Ioc (-2 * Real.pi) (2 * Real.pi) ×ˢ Ioc (-2 * Real.pi) (2 * Real.pi) := by
    rintro p ⟨ha, hb⟩
    simp only [diagCoord, abs_lt] at ha hb
    exact ⟨⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩,
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩⟩
  have hsq (g : L2) : IntegrableOn (fun p ↦ ‖liftL2 g p‖ ^ 2) cellSquare :=
    (integrableOn_norm_liftL2_sq g).mono_set hsub
  have iu : IntegrableOn (fun p ↦ ‖u p‖ ^ 2) cellSquare := by
    apply (hsq φ).congr
    filter_upwards [ae_restrict_of_ae (ae_torusProj (coeFn_eq_continuousRep hφ))]
      with p hp
    exact congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hp
  let F := fun p ↦ ‖u p‖ ^ 2 + ‖liftL2 dx p‖ ^ 2 +
    ‖liftL2 dy p‖ ^ 2 + ‖liftL2 ν p‖ ^ 2
  have iF : IntegrableOn F cellSquare := ((iu.add (hsq dx)).add (hsq dy)).add (hsq ν)
  have hn (p) : ‖n p‖ ^ 2 ≤ 2 * F p := by
    have hb := norm_normalDeriv_le (liftL2 dx) (liftL2 dy) p
    have he : ‖n p‖ = ‖normalDeriv (liftL2 dx) (liftL2 dy) p‖ := norm_neg _
    dsimp only [F]
    rw [← he] at hb
    nlinarith [sq_nonneg (‖liftL2 dx p‖ - ‖liftL2 dy p‖),
      norm_nonneg (n p), norm_nonneg (liftL2 dx p), norm_nonneg (liftL2 dy p),
      sq_nonneg ‖u p‖, sq_nonneg ‖liftL2 ν p‖]
  have ht (p) : ‖τ p‖ ^ 2 ≤ 2 * F p := by
    have hb := norm_tangentDeriv_le (liftL2 dx) (liftL2 dy) p
    dsimp only [F]
    nlinarith [sq_nonneg (‖liftL2 dx p‖ - ‖liftL2 dy p‖),
      norm_nonneg (τ p), norm_nonneg (liftL2 dx p), norm_nonneg (liftL2 dy p),
      sq_nonneg ‖u p‖, sq_nonneg ‖liftL2 ν p‖]
  have hre (a b : ℂ) : |(a * (starRingEnd ℂ) b).re| ≤ ‖a‖ * ‖b‖ := by
    exact (Complex.abs_re_le_norm _).trans (by rw [norm_mul, Complex.norm_conj])
  have hp (p) : |(liftL2 ν p * (starRingEnd ℂ) (u p)).re| ≤ F p := by
    refine (hre _ _).trans ?_
    dsimp only [F]
    nlinarith [sq_nonneg (‖liftL2 ν p‖ - ‖u p‖),
      sq_nonneg ‖liftL2 dx p‖, sq_nonneg ‖liftL2 dy p‖]
  have hr (p) : gradNorm p ≤ 2 := by
    have h0 : 0 ≤ gradNorm p := Real.sqrt_nonneg _
    have h2 : gradNorm p ^ 2 ≤ 2 := by
      rw [gradNorm, Real.sq_sqrt (by positivity)]
      nlinarith [Real.sin_sq_le_one p.1, Real.sin_sq_le_one p.2]
    nlinarith
  have hm (p) : |gradNorm p * ((starRingEnd ℂ) (u p) * n p).re| ≤ 3 * F p := by
    rw [abs_mul, abs_of_nonneg (show 0 ≤ gradNorm p from Real.sqrt_nonneg _)]
    have hu : ‖u p‖ ^ 2 ≤ F p := by
      dsimp only [F]
      nlinarith [sq_nonneg (‖liftL2 dx p‖), sq_nonneg (‖liftL2 dy p‖),
        sq_nonneg (‖liftL2 ν p‖)]
    have hb : |((starRingEnd ℂ) (u p) * n p).re| ≤ ‖u p‖ * ‖n p‖ := by
      simpa [mul_comm] using hre (n p) (u p)
    nlinarith [mul_le_mul (hr p) hb (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
      hn p, sq_nonneg (‖u p‖ - ‖n p‖)]
  have iN : IntegrableOn (fun p ↦ ‖n p‖ ^ 2) cellSquare :=
    (iF.const_mul 2).mono' (mn.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hn p)
  have iT : IntegrableOn (fun p ↦ ‖τ p‖ ^ 2) cellSquare :=
    (iF.const_mul 2).mono' (mt.norm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact ht p)
  have iP : IntegrableOn (fun p ↦ (liftL2 ν p * (starRingEnd ℂ) (u p)).re) cellSquare :=
    iF.mono' (by fun_prop) (Eventually.of_forall fun p ↦ hp p)
  have iM : IntegrableOn (fun p ↦ gradNorm p * ((starRingEnd ℂ) (u p) * n p).re)
      cellSquare :=
    (iF.const_mul 3).mono' (by fun_prop) (Eventually.of_forall fun p ↦ hm p)
  filter_upwards [(integral_cellSquare_eq iN).1, (integral_cellSquare_eq iT).1,
    (integral_cellSquare_eq iu).1, (integral_cellSquare_eq iP).1,
    (integral_cellSquare_eq iM).1, ae_restrict_mem measurableSet_Ioo]
    with h jN jT jU jP jM hh
  simp only [ddVirialLevel, ddLevelMass, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
    levelIntegral_eq_integral_orbitWindow hh.1 hh.2]
  change (∫ t in Ico (-2 * eighthPeriod h) (6 * eighthPeriod h),
    (8 - (2 * h) ^ 3) / 3 * (‖n (dipoleOrbit h t)‖ ^ 2 - ‖τ (dipoleOrbit h t)‖ ^ 2 -
      ‖u (dipoleOrbit h t)‖ ^ 2 + (-liftL2 ν (dipoleOrbit h t) *
        (starRingEnd ℂ) (u (dipoleOrbit h t))).re) -
      (2 * h) ^ 2 * gradNorm (dipoleOrbit h t) *
        ((starRingEnd ℂ) (u (dipoleOrbit h t)) * n (dipoleOrbit h t)).re) = _
  simp only [neg_mul, Complex.neg_re, ← sub_eq_add_neg]
  simp_rw [mul_assoc ((2 * h) ^ 2)]
  simp only [neg_mul] at jN jT jU jP jM
  have hsplit := integral_sub
    ((((jN.sub jT).sub jU).sub jP).const_mul ((8 - (2 * h) ^ 3) / 3))
    (jM.const_mul ((2 * h) ^ 2))
  simp only [Pi.sub_apply] at hsplit
  rw [hsplit, integral_const_mul, integral_const_mul]
  have h1 := integral_sub ((jN.sub jT).sub jU) jP
  have h2 := integral_sub (jN.sub jT) jU
  have h3 := integral_sub jN jT
  simp only [Pi.sub_apply] at h1 h2 h3
  rw [h1, h2, h3]

end NoEmbeddedEigenvalues
