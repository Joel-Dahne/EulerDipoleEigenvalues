module

public import NoEmbeddedEigenvalues.EvenEven.TraceExclusion.EigenfunctionTransport

/-!
# Pointwise parity of the continuous stream

Blueprint: `lem:continuous-stream-zero-separatrix`.

The continuous Fourier representative inherits a.e. reflection identities
everywhere. Only this representative, not raw L² values on the fixed lines,
is evaluated on the separatrix.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

private theorem continuousRep_invLap_parity {ω : L2} {T : Torus → Torus}
    {hT : MeasurePreserving T} (hTc : Continuous T) {χ : ℂ}
    (hs : pullback T hT (invLap ω) = χ • invLap ω) :
    ∀ t, continuousRep (invLap ω) (T t) = χ * continuousRep (invLap ω) t := by
  have hi := coeFn_invLap_eq_continuousRep ω
  have hc := hT.quasiMeasurePreserving.ae_eq_comp hi
  have ha := ae_comp_of_pullback_eq hs
  have he : (fun t ↦ continuousRep (invLap ω) (T t)) =ᵐ[volume]
      (fun t ↦ χ * continuousRep (invLap ω) t) := by
    filter_upwards [hi, hc, ha, Lp.coeFn_smul χ (invLap ω)] with t hi hc ha hsm
    dsimp only [Function.comp_apply] at hc
    rw [← hc, ha, hsm]
    change χ * invLap ω t = _
    rw [hi]
  have : (volume : Measure Torus).IsOpenPosMeasure := by
    change (volume : Measure (AddCircle (2 * Real.pi) × AddCircle (2 * Real.pi))).IsOpenPosMeasure
    infer_instance
  exact congrFun (Measure.eq_of_ae_eq he
    ((continuousRep (invLap ω)).continuous.comp hTc)
    (continuous_const.mul (continuousRep (invLap ω)).continuous))

/-- Odd parity under the first reflection also forces zero stream values
on its fixed lines, independently of the parity under the second reflection. -/
theorem contStream_eq_zero_of_odd_first {ω : L2} {b : Bool} (hs : InSector false b ω)
    {p : ℝ × ℝ} (hp : (torusProj p).1 + (torusProj p).2 = Real.pi) : contStream ω p = 0 := by
  have h := continuousRep_invLap_parity (show Continuous S₁ by unfold S₁; fun_prop)
    hs.invLap.1 (torusProj p)
  rw [(S₁_eq_self_iff _).mpr hp] at h
  change contStream ω p = paritySign false * contStream ω p at h
  simp only [paritySign, Bool.false_eq_true, ite_false, neg_one_mul] at h
  exact CharZero.eq_neg_self_iff.mp h

/-- Odd parity under both reflections forces the continuous stream to vanish
on every lifted separatrix line, including saddles. -/
theorem contStream_eq_zero_on_separatrix {ω : L2} (hs : InSector false false ω)
    {p : ℝ × ℝ} (hp : dipoleLift p = 0) : contStream ω p = 0 := by
  have h1 := continuousRep_invLap_parity (show Continuous S₁ by unfold S₁; fun_prop)
    hs.invLap.1
  have h2 := continuousRep_invLap_parity (show Continuous S₂ by unfold S₂; fun_prop)
    hs.invLap.2
  have hz : Ψ (torusProj p) = 0 := by rwa [Ψ_torusProj]
  rcases (Ψ_eq_zero_iff _).mp hz with hp | hp
  · have he := h1 (torusProj p)
    rw [(S₁_eq_self_iff _).mpr hp] at he
    change contStream ω p = paritySign false * contStream ω p at he
    simp only [paritySign, Bool.false_eq_true, ite_false, neg_one_mul] at he
    exact CharZero.eq_neg_self_iff.mp he
  · have he := h2 (torusProj p)
    rw [(S₂_eq_self_iff _).mpr hp] at he
    change contStream ω p = paritySign false * contStream ω p at he
    simp only [paritySign, Bool.false_eq_true, ite_false, neg_one_mul] at he
    exact CharZero.eq_neg_self_iff.mp he

end NoEmbeddedEigenvalues
