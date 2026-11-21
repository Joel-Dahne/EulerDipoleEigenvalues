import NoEmbeddedEigenvalues.OddOdd.Picone.ZonalModes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Order.ProjIcc

/-!
# The weighted product zonal basis

Blueprint: `lem:zonal-mode-basis`. The measure is the probability normalization
of `cos² a cos² b da db` on the diagonal square. Values on its boundary do not
matter. Completeness follows from Stone–Weierstrass: Chebyshev polynomials
span all polynomials in the two sine coordinates, which separate points on
the compact square. Retraction extensions transfer this uniform density to
weighted L². This is separate from all weak derivative and weighted Sobolev
questions. `zonalBasis_repr` and `hasSum_sq_zonalCoeff` identify the Hilbert
coordinates with the raw weighted integrals, including their normalization.
-/

noncomputable section
namespace NoEmbeddedEigenvalues

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Polynomial

/-- The open diagonal square. -/
def zonalSquare : Set (ℝ × ℝ) :=
  Ioo (-Real.pi / 2) (Real.pi / 2) ×ˢ Ioo (-Real.pi / 2) (Real.pi / 2)

/-- The normalized weighted measure on the diagonal square. -/
def zonalMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict zonalSquare).withDensity (fun p ↦
    ENNReal.ofReal (4 / Real.pi ^ 2 * (Real.cos p.1 ^ 2 * Real.cos p.2 ^ 2)))

/-- Real product mode, evaluated on the whole plane. -/
def zonalProduct (k : ℕ × ℕ) (p : ℝ × ℝ) : ℝ :=
  zonalMode k.1 p.1 * zonalMode k.2 p.2

private theorem integral_cos_int (k : ℤ) :
    (∫ t in (0 : ℝ)..Real.pi, Real.cos ((k : ℝ) * t)) =
      if k = 0 then Real.pi else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · rw [ite_eq_right hk, intervalIntegral.integral_comp_mul_left Real.cos
      (show (k : ℝ) ≠ 0 by exact_mod_cast hk), integral_cos]
    simp [Real.sin_int_mul_pi]

private theorem integral_sine_product (n m : ℕ) :
    (∫ t in (0 : ℝ)..Real.pi,
      Real.sin (((n : ℝ) + 1) * t) * Real.sin (((m : ℝ) + 1) * t)) =
      if n = m then Real.pi / 2 else 0 := by
  have hfun : (fun t : ℝ ↦ Real.sin (((n : ℝ) + 1) * t) *
      Real.sin (((m : ℝ) + 1) * t)) =
      (fun t ↦ (Real.cos (((n : ℤ) - m : ℤ) * t) -
        Real.cos (((n : ℤ) + m + 2 : ℤ) * t)) / 2) := by
    funext t
    push_cast
    rw [show ((n : ℝ) - m) * t = ((n : ℝ) + 1) * t - ((m : ℝ) + 1) * t by ring,
      show ((n : ℝ) + m + 2) * t = ((n : ℝ) + 1) * t + ((m : ℝ) + 1) * t by ring,
      Real.cos_sub, Real.cos_add]
    ring
  rw [hfun, intervalIntegral.integral_div,
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    integral_cos_int, integral_cos_int]
  have hsum : (n : ℤ) + m + 2 ≠ 0 := by omega
  simp only [hsum, ite_false, sub_zero]
  by_cases hnm : n = m <;> simp [sub_eq_zero, hnm]

/-- Exact one-dimensional weighted orthogonality. -/
theorem integral_zonalMode_mul (n m : ℕ) :
    (∫ a in Ioo (-Real.pi / 2) (Real.pi / 2),
      Real.cos a ^ 2 * (zonalMode n a * zonalMode m a)) =
      if n = m then Real.pi / 2 else 0 := by
  have hab : -Real.pi / 2 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
  have hfun : (fun a ↦ Real.cos a ^ 2 * (zonalMode n a * zonalMode m a)) =
      (fun a ↦ Real.sin (((n : ℝ) + 1) * (Real.pi / 2 - a)) *
        Real.sin (((m : ℝ) + 1) * (Real.pi / 2 - a))) := by
    funext a
    rw [← zonalMode_mul_cos, ← zonalMode_mul_cos]
    ring
  rw [hfun, intervalIntegral.integral_comp_sub_left
    (fun t : ℝ ↦ Real.sin (((n : ℝ) + 1) * t) * Real.sin (((m : ℝ) + 1) * t))
    (Real.pi / 2)]
  convert integral_sine_product n m using 1
  congr 1 <;> ring

private theorem integral_cos_sq_Ioo :
    (∫ a in Ioo (-Real.pi / 2) (Real.pi / 2), Real.cos a ^ 2) = Real.pi / 2 := by
  simpa using integral_zonalMode_mul 0 0

private theorem weight_integrable : IntegrableOn
    (fun p : ℝ × ℝ ↦ 4 / Real.pi ^ 2 * (Real.cos p.1 ^ 2 * Real.cos p.2 ^ 2)) zonalSquare := by
  have hc : Continuous (fun p : ℝ × ℝ ↦
      4 / Real.pi ^ 2 * (Real.cos p.1 ^ 2 * Real.cos p.2 ^ 2)) := by fun_prop
  exact (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)

/-- Integral formula retaining the physical normalization. -/
theorem integral_zonalMeasure (f : ℝ × ℝ → ℝ) :
    ∫ p, f p ∂zonalMeasure =
      4 / Real.pi ^ 2 * ∫ p in zonalSquare,
        (Real.cos p.1 ^ 2 * Real.cos p.2 ^ 2) * f p := by
  rw [zonalMeasure, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (by simp)]
  have hpos (p : ℝ × ℝ) :
      0 ≤ 4 / Real.pi ^ 2 * (Real.cos p.1 ^ 2 * Real.cos p.2 ^ 2) := by positivity
  simp only [ENNReal.toReal_ofReal (hpos _), smul_eq_mul]
  simp_rw [mul_assoc]
  exact integral_const_mul _ _

/-- The normalization makes the weighted square a probability space. -/
instance zonalMeasure_isProbabilityMeasure : IsProbabilityMeasure zonalMeasure := by
  have hpos : ∀ p : ℝ × ℝ, 0 ≤ 4 / Real.pi ^ 2 *
      (Real.cos p.1 ^ 2 * Real.cos p.2 ^ 2) := fun _ ↦ by positivity
  have hint : (∫ p in zonalSquare, 4 / Real.pi ^ 2 *
      (Real.cos p.1 ^ 2 * Real.cos p.2 ^ 2)) = 1 := by
    rw [integral_const_mul, zonalSquare, Measure.volume_eq_prod,
      setIntegral_prod_mul (fun a : ℝ ↦ Real.cos a ^ 2) (fun b : ℝ ↦ Real.cos b ^ 2),
      integral_cos_sq_Ioo]
    field_simp
    ring
  constructor
  rw [zonalMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal weight_integrable
      (Filter.Eventually.of_forall hpos), hint, ENNReal.ofReal_one]

/-- The weighted measure is supported on the open square. -/
theorem ae_mem_zonalSquare : ∀ᵐ p ∂zonalMeasure, p ∈ zonalSquare :=
  (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo))

/-- Exact orthogonality of the raw product modes. -/
theorem integral_zonalProduct_mul (k l : ℕ × ℕ) :
    (∫ p, zonalProduct k p * zonalProduct l p ∂zonalMeasure) = if k = l then 1 else 0 := by
  rw [integral_zonalMeasure]
  have heq : (fun p ↦ (Real.cos p.1 ^ 2 * Real.cos p.2 ^ 2) *
      (zonalProduct k p * zonalProduct l p)) =
      (fun p ↦ (Real.cos p.1 ^ 2 * (zonalMode k.1 p.1 * zonalMode l.1 p.1)) *
        (Real.cos p.2 ^ 2 * (zonalMode k.2 p.2 * zonalMode l.2 p.2))) := by
    funext p
    simp only [zonalProduct]
    ring
  rw [heq, zonalSquare, Measure.volume_eq_prod, setIntegral_prod_mul
    (fun a : ℝ ↦ Real.cos a ^ 2 * (zonalMode k.1 a * zonalMode l.1 a))
    (fun b : ℝ ↦ Real.cos b ^ 2 * (zonalMode k.2 b * zonalMode l.2 b)),
    integral_zonalMode_mul, integral_zonalMode_mul]
  by_cases h1 : k.1 = l.1 <;> by_cases h2 : k.2 = l.2
  · have hk : k = l := Prod.ext h1 h2
    simp only [hk, ite_true]
    field_simp
    ring
  all_goals have hk : k ≠ l := by intro h; cases h; contradiction
  all_goals simp [h1, h2, hk]

/-- The compact interval is used only for uniform approximation of continuous
functions, not as a boundary condition on weighted Sobolev data. -/
abbrev ZonalInterval := Icc (-Real.pi / 2) (Real.pi / 2)

abbrev ZonalCompactSquare := ZonalInterval × ZonalInterval

private theorem zonalInterval_le : -Real.pi / 2 ≤ Real.pi / 2 := by linarith [Real.pi_pos]

/-- Coordinatewise retraction onto the compact square. -/
def zonalClamp : C(ℝ × ℝ, ZonalCompactSquare) :=
  ⟨fun p ↦ (projIcc _ _ zonalInterval_le p.1, projIcc _ _ zonalInterval_le p.2),
    (continuous_projIcc.comp continuous_fst).prodMk (continuous_projIcc.comp continuous_snd)⟩

/-- The product modes as continuous functions on the compact square. -/
def zonalModeCM (k : ℕ × ℕ) : C(ZonalCompactSquare, ℂ) :=
  ⟨fun p ↦ (zonalProduct k (p.1, p.2) : ℂ), by
    unfold zonalProduct
    exact Complex.continuous_ofReal.comp
      (((contDiff_zonalMode k.1).continuous.comp (continuous_subtype_val.comp continuous_fst)).mul
        ((contDiff_zonalMode k.2).continuous.comp (continuous_subtype_val.comp continuous_snd)))⟩

/-- Extend a compact-square continuous function by retraction and pass to its
weighted L² class. -/
def zonalToLp : C(ZonalCompactSquare, ℂ) →L[ℂ] Lp ℂ 2 zonalMeasure :=
  (BoundedContinuousFunction.toLp 2 zonalMeasure ℂ).comp
    ((BoundedContinuousFunction.compContinuousCLM ℂ ℂ zonalClamp).comp
      (ContinuousMap.linearIsometryBoundedOfCompact
        ZonalCompactSquare ℂ ℂ).toContinuousLinearEquiv.toContinuousLinearMap)

/-- Bundled weighted product mode. -/
def zonalModeLp (k : ℕ × ℕ) : Lp ℂ 2 zonalMeasure := zonalToLp (zonalModeCM k)

theorem coeFn_zonalToLp (f : C(ZonalCompactSquare, ℂ)) :
    zonalToLp f =ᵐ[zonalMeasure] (fun p ↦ f (zonalClamp p)) := by
  exact BoundedContinuousFunction.coeFn_toLp 2 zonalMeasure ℂ
    (((ContinuousMap.linearIsometryBoundedOfCompact
      ZonalCompactSquare ℂ ℂ) f).compContinuous zonalClamp)

theorem coeFn_zonalModeLp (k : ℕ × ℕ) :
    zonalModeLp k =ᵐ[zonalMeasure] (fun p ↦ (zonalProduct k p : ℂ)) := by
  have h := BoundedContinuousFunction.coeFn_toLp 2 zonalMeasure ℂ
    (((ContinuousMap.linearIsometryBoundedOfCompact ZonalCompactSquare ℂ ℂ)
      (zonalModeCM k)).compContinuous zonalClamp)
  filter_upwards [h, ae_mem_zonalSquare] with p hp hmem
  change zonalModeLp k p = zonalModeCM k (zonalClamp p) at hp
  rw [hp]
  change (zonalProduct k ((projIcc _ _ zonalInterval_le p.1 : ZonalInterval),
    (projIcc _ _ zonalInterval_le p.2 : ZonalInterval)) : ℂ) = _
  rw [projIcc_of_mem _ ⟨hmem.1.1.le, hmem.1.2.le⟩,
    projIcc_of_mem _ ⟨hmem.2.1.le, hmem.2.2.le⟩]

theorem inner_zonalModeLp (k l : ℕ × ℕ) :
    ⟪zonalModeLp k, zonalModeLp l⟫_ℂ = if k = l then 1 else 0 := by
  rw [MeasureTheory.L2.inner_def]
  have heq : (fun p ↦ inner ℂ (zonalModeLp k p) (zonalModeLp l p)) =ᵐ[zonalMeasure]
      (fun p ↦ ((zonalProduct k p * zonalProduct l p : ℝ) : ℂ)) := by
    filter_upwards [coeFn_zonalModeLp k, coeFn_zonalModeLp l] with p hk hl
    simp [hk, hl, RCLike.inner_apply, mul_comm]
  rw [integral_congr_ae heq, integral_complex_ofReal, integral_zonalProduct_mul]
  split_ifs <;> norm_num

theorem orthonormal_zonalModeLp : Orthonormal ℂ zonalModeLp :=
  orthonormal_iff_ite.mpr inner_zonalModeLp

private def zonalSinFst : C(ZonalCompactSquare, ℂ) :=
  ⟨fun p ↦ (Real.sin p.1 : ℂ), by fun_prop⟩

private def zonalSinSnd : C(ZonalCompactSquare, ℂ) :=
  ⟨fun p ↦ (Real.sin p.2 : ℂ), by fun_prop⟩

private def zonalPolynomial (p q : ℂ[X]) : C(ZonalCompactSquare, ℂ) :=
  Polynomial.aeval zonalSinFst p * Polynomial.aeval zonalSinSnd q

private def zonalCMSpan : Submodule ℂ C(ZonalCompactSquare, ℂ) :=
  Submodule.span ℂ (range zonalModeCM)

private def zonalUSequence : Polynomial.Sequence ℂ where
  elems' n := Polynomial.Chebyshev.U ℂ (n : ℤ)
  degree_eq' n := Polynomial.Chebyshev.degree_U_natCast ℂ n

private theorem span_zonalUSequence :
    Submodule.span ℂ (range (fun n : ℕ ↦ Polynomial.Chebyshev.U ℂ (n : ℤ))) = ⊤ := by
  apply zonalUSequence.span
  intro n
  apply isUnit_iff_ne_zero.mpr
  change (Polynomial.Chebyshev.U ℂ (n : ℤ)).leadingCoeff ≠ 0
  rw [Polynomial.Chebyshev.leadingCoeff_U_natCast]
  exact pow_ne_zero _ (by norm_num)

private theorem zonalPolynomial_U (n m : ℕ) :
    zonalPolynomial (Polynomial.Chebyshev.U ℂ (n : ℤ))
      (Polynomial.Chebyshev.U ℂ (m : ℤ)) = zonalModeCM (n, m) := by
  ext p
  change ((Polynomial.aeval zonalSinFst) (Polynomial.Chebyshev.U ℂ (n : ℤ))) p *
    ((Polynomial.aeval zonalSinSnd) (Polynomial.Chebyshev.U ℂ (m : ℤ))) p = _
  rw [Polynomial.aeval_continuousMap_apply, Polynomial.aeval_continuousMap_apply]
  change (Polynomial.Chebyshev.U ℂ (n : ℤ)).eval (algebraMap ℝ ℂ (Real.sin p.1)) *
    (Polynomial.Chebyshev.U ℂ (m : ℤ)).eval (algebraMap ℝ ℂ (Real.sin p.2)) = _
  rw [← Polynomial.Chebyshev.algebraMap_eval_U, ← Polynomial.Chebyshev.algebraMap_eval_U,
    ← map_mul]
  rfl

private theorem zonalPolynomial_mem_span (p q : ℂ[X]) : zonalPolynomial p q ∈ zonalCMSpan := by
  have hp : p ∈ Submodule.span ℂ (range (fun n : ℕ ↦ Polynomial.Chebyshev.U ℂ (n : ℤ))) := by
    rw [span_zonalUSequence]; trivial
  have hq : q ∈ Submodule.span ℂ (range (fun n : ℕ ↦ Polynomial.Chebyshev.U ℂ (n : ℤ))) := by
    rw [span_zonalUSequence]; trivial
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨n, rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨m, rfl⟩ := hq
      rw [zonalPolynomial_U]
      exact Submodule.subset_span ⟨(n, m), rfl⟩
    | zero => simp [zonalPolynomial, zonalCMSpan]
    | add q r _ _ hq hr =>
      simpa [zonalPolynomial, map_add, mul_add] using zonalCMSpan.add_mem hq hr
    | smul a q _ hq =>
      simpa [zonalPolynomial, map_smul, mul_smul_comm] using zonalCMSpan.smul_mem a hq
  | zero => simp [zonalPolynomial, zonalCMSpan]
  | add p r _ _ hp hr =>
    simpa [zonalPolynomial, map_add, add_mul] using zonalCMSpan.add_mem hp hr
  | smul a p _ hp =>
    simpa [zonalPolynomial, map_smul, smul_mul_assoc] using zonalCMSpan.smul_mem a hp

private theorem zonalCMSpan_mul {f g : C(ZonalCompactSquare, ℂ)}
    (hf : f ∈ zonalCMSpan) (hg : g ∈ zonalCMSpan) : f * g ∈ zonalCMSpan := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨l, rfl⟩ := hg
      have heq : zonalModeCM k * zonalModeCM l =
          zonalPolynomial (Polynomial.Chebyshev.U ℂ (k.1 : ℤ) *
            Polynomial.Chebyshev.U ℂ (l.1 : ℤ))
            (Polynomial.Chebyshev.U ℂ (k.2 : ℤ) * Polynomial.Chebyshev.U ℂ (l.2 : ℤ)) := by
        rw [zonalPolynomial, map_mul, map_mul]
        conv_lhs => rw [← zonalPolynomial_U k.1 k.2, ← zonalPolynomial_U l.1 l.2]
        unfold zonalPolynomial
        ring
      rw [heq]
      exact zonalPolynomial_mem_span _ _
    | zero => simp
    | add g h _ _ hg hh => simpa [mul_add] using zonalCMSpan.add_mem hg hh
    | smul a g _ hg => simpa [mul_smul_comm] using zonalCMSpan.smul_mem a hg
  | zero => simp
  | add f h _ _ hf hh => simpa [add_mul] using zonalCMSpan.add_mem hf hh
  | smul a f _ hf => simpa [smul_mul_assoc] using zonalCMSpan.smul_mem a hf

private theorem zonalCMSpan_star {f : C(ZonalCompactSquare, ℂ)}
    (hf : f ∈ zonalCMSpan) : star f ∈ zonalCMSpan := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, rfl⟩ := hf
    have heq : star (zonalModeCM k) = zonalModeCM k := by
      ext p
      simp [zonalModeCM]
    rw [heq]
    exact Submodule.subset_span ⟨k, rfl⟩
  | zero => simp
  | add f g _ _ hf hg => simpa using zonalCMSpan.add_mem hf hg
  | smul a f _ hf => simpa using zonalCMSpan.smul_mem (star a) hf

private def zonalCMAlgebra : StarSubalgebra ℂ C(ZonalCompactSquare, ℂ) where
  toSubalgebra := zonalCMSpan.toSubalgebra (by
    have h := zonalPolynomial_mem_span 1 1
    simpa [zonalPolynomial] using h) (fun _ _ ↦ zonalCMSpan_mul)
  star_mem' := zonalCMSpan_star

private theorem zonalCMAlgebra_separatesPoints : zonalCMAlgebra.SeparatesPoints := by
  have hfst : zonalSinFst ∈ zonalCMAlgebra := by
    change zonalSinFst ∈ zonalCMSpan
    simpa [zonalPolynomial] using zonalPolynomial_mem_span Polynomial.X 1
  have hsnd : zonalSinSnd ∈ zonalCMAlgebra := by
    change zonalSinSnd ∈ zonalCMSpan
    simpa [zonalPolynomial] using zonalPolynomial_mem_span 1 Polynomial.X
  intro x y hxy
  by_cases h1 : x.1 = y.1
  · have h2 : x.2 ≠ y.2 := fun h2 ↦ hxy (Prod.ext h1 h2)
    refine ⟨_, ⟨zonalSinSnd, hsnd, rfl⟩, fun heq ↦ h2 ?_⟩
    apply Subtype.ext
    apply Real.injOn_sin
      (by simpa only [ZonalInterval, neg_div] using x.2.property)
      (by simpa only [ZonalInterval, neg_div] using y.2.property)
    change (Real.sin (x.2 : ℝ) : ℂ) = (Real.sin (y.2 : ℝ) : ℂ) at heq
    exact Complex.ofReal_injective heq
  · refine ⟨_, ⟨zonalSinFst, hfst, rfl⟩, fun heq ↦ h1 ?_⟩
    apply Subtype.ext
    apply Real.injOn_sin
      (by simpa only [ZonalInterval, neg_div] using x.1.property)
      (by simpa only [ZonalInterval, neg_div] using y.1.property)
    change (Real.sin (x.1 : ℝ) : ℂ) = (Real.sin (y.1 : ℝ) : ℂ) at heq
    exact Complex.ofReal_injective heq

/-- Uniform completeness of product zonal modes on the compact square. -/
theorem span_zonalModeCM_closure_eq_top :
    (Submodule.span ℂ (range zonalModeCM)).topologicalClosure = ⊤ := by
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    zonalCMAlgebra zonalCMAlgebra_separatesPoints
  exact congrArg (fun A : StarSubalgebra ℂ C(ZonalCompactSquare, ℂ) ↦
    A.toSubalgebra.toSubmodule) h

/-- Retraction extensions have dense range in weighted L². -/
theorem zonalToLp_denseRange : DenseRange zonalToLp := by
  refine (BoundedContinuousFunction.toLp_denseRange ℂ zonalMeasure ℂ (by norm_num)).mono ?_
  rintro _ ⟨g, rfl⟩
  let f : C(ZonalCompactSquare, ℂ) := ⟨fun p ↦ g (p.1, p.2), by fun_prop⟩
  refine ⟨f, ?_⟩
  apply Lp.ext
  filter_upwards [coeFn_zonalToLp f, g.coeFn_toLp 2 zonalMeasure ℂ, ae_mem_zonalSquare]
    with p hf hg hmem
  rw [hf, hg]
  change g ((projIcc _ _ zonalInterval_le p.1 : ZonalInterval),
    (projIcc _ _ zonalInterval_le p.2 : ZonalInterval)) = g p
  rw [projIcc_of_mem _ ⟨hmem.1.1.le, hmem.1.2.le⟩,
    projIcc_of_mem _ ⟨hmem.2.1.le, hmem.2.2.le⟩]

/-- Completeness in the whole weighted L² space, without Sobolev assumptions. -/
theorem span_zonalModeLp_closure_eq_top :
    (Submodule.span ℂ (range zonalModeLp)).topologicalClosure = ⊤ := by
  change (Submodule.span ℂ (range (fun k ↦ zonalToLp (zonalModeCM k)))).topologicalClosure = ⊤
  simpa only [Submodule.map_span, ContinuousLinearMap.coe_coe, ← range_comp,
    Function.comp_def] using
    zonalToLp_denseRange.topologicalClosure_map_submodule span_zonalModeCM_closure_eq_top

/-- The weighted product Chebyshev Hilbert basis. -/
def zonalBasis : HilbertBasis (ℕ × ℕ) ℂ (Lp ℂ 2 zonalMeasure) :=
  HilbertBasis.mk orthonormal_zonalModeLp span_zonalModeLp_closure_eq_top.ge

theorem zonalBasis_apply (k : ℕ × ℕ) : zonalBasis k = zonalModeLp k :=
  congrFun (HilbertBasis.coe_mk _ _) k

/-- Hilbert coordinates are precisely the raw weighted mode integrals. -/
theorem zonalBasis_repr (z : Lp ℂ 2 zonalMeasure) (k : ℕ × ℕ) :
    zonalBasis.repr z k = ∫ p, (zonalProduct k p : ℂ) * z p ∂zonalMeasure := by
  rw [HilbertBasis.repr_apply_apply, zonalBasis_apply, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_zonalModeLp k] with p hk
  simp [hk, RCLike.inner_apply, mul_comm]

/-- Parseval for the explicit weighted product-mode coefficients. -/
theorem hasSum_sq_zonalCoeff (z : Lp ℂ 2 zonalMeasure) :
    HasSum (fun k : ℕ × ℕ ↦ ‖∫ p, (zonalProduct k p : ℂ) * z p ∂zonalMeasure‖ ^ 2)
      (‖z‖ ^ 2) := by
  have h := lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (zonalBasis.repr z)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map,
    zonalBasis_repr] using h

end NoEmbeddedEigenvalues
