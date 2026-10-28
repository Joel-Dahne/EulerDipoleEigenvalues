import NoEmbeddedEigenvalues.EigenfunctionTransport
import NoEmbeddedEigenvalues.Derivatives

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
  obtain ⟨φ, hφ, hψ⟩ : ∃ φ : L2, MemSobolev 2 φ ∧
      ∀ᵐ t, invLap ω t = (Ψ t : ℂ) * φ t := by
    -- Construct the H² quotient using local division and periodic gluing.
    sorry
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

/-- Periodic weak invariant division (`cor:dd-quotient-transport-periodic`).
Only the L² quotients and their multiplication identities are assumed; neither H¹
regularity of ν nor corner weights are hypotheses. -/
theorem dd_quotient_transport {lam : ℝ} {ω ψ ν φ : L2}
    (h : HasL0 (ω + ψ) ((Complex.I * lam) • ω))
    (hψ : ∀ᵐ t, ψ t = (Ψ t : ℂ) * φ t)
    (hω : ∀ᵐ t, ω t = (Ψ t : ℂ) * ν t) :
    HasL0 (ν + φ) ((Complex.I * lam) • ν) := by
  sorry

/-- Periodic first transport gain on the full fixed lift neighbourhood
(`cor:transport-first-gain-periodic`), including reflection and periodic cell covering.
No parity, elliptic relation or vanishing saddle value of the forcing is assumed. -/
theorem transport_first_gain_periodic {lam : ℝ} (hlam : lam ≠ 0) {ν φ : L2}
    (hφ : MemSobolev 2 φ) (h : HasL0 (ν + φ) ((Complex.I * lam) • ν)) :
    MemLp (fun p ↦ liftL2 ν p / (saddleDist p : ℂ)) 2
      (volume.restrict cellNeighbourhood) := by
  sorry

/-- A periodic weak transport relation gives a transport pair with continuous forcing
on any bounded open union of orbits (`lem:periodic-transport-pair`). -/
theorem isTransportPair_continuousRep {lam : ℝ} (hlam : lam ≠ 0) {ν φ : L2}
    (hφ : MemSobolev 2 φ) (h : HasL0 (ν + φ) ((Complex.I * lam) • ν))
    {U : Set (ℝ × ℝ)} (hU : IsOrbitUnion U) (hb : Bornology.IsBounded U) :
    IsTransportPair lam U (liftL2 ν) (fun p ↦ continuousRep φ (torusProj p)) := by
  have heq : liftL2 φ =ᵐ[volume] (fun p ↦ continuousRep φ (torusProj p)) :=
    ae_torusProj (coeFn_eq_continuousRep hφ)
  refine ⟨hlam, hU, memLp_liftL2 ν hb, (memSobolevOn_liftL2 hφ hb).congr_ae heq, ?_⟩
  refine ((hasWeakL0On_liftL2 h U).congr_value ?_).congr_deriv ?_
  · filter_upwards [liftL2_add_ae ν φ, heq] with p hp hφp
    rw [hp, hφp]
  · filter_upwards [liftL2_smul_ae (Complex.I * lam) ν] with p hp
    rw [hp, mul_assoc]

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
