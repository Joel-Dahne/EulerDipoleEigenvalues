import NoEmbeddedEigenvalues.PeriodicTransportGain
import NoEmbeddedEigenvalues.Derivatives
import NoEmbeddedEigenvalues.Regularity.StreamQuotientAssembly

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

/-- Coordinate Hardy controls the divided Laplacian of an even H² function
(`lem:even-h2-dipole-laplacian`). The Laplacian is specified by its Fourier relation;
no classical second derivative of an arbitrary L² representative is used. -/
theorem even_h2_dipole_laplacian {φ ψ ζ : L2} (hφ : MemSobolev 2 φ)
    (hs : InSector true true φ) (hψ : ∀ᵐ t, ψ t = (Ψ t : ℂ) * φ t)
    (hΔ : HasFourierLaplacian ψ ζ) :
    ∃ ν : L2, ∀ᵐ t, ζ t = (Ψ t : ℂ) * ν t := by
  sorry

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
