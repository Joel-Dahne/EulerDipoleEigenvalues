import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderFourierRoundtrip
import NoEmbeddedEigenvalues.Regularity.SaddleElliptic.CylinderJetCandidates

/-!
# The forcing identity for the specified L² inverse entries

Linearity and the normalized Fourier round-trip transfer the spectral multiplier
equation to an a.e. algebraic equation among the actual candidate entries.
No weak derivative identity is inferred from this equation.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory

/-- The scalar symbol is exactly the ordered-jet polynomial, also for negative modes. -/
theorem cylinderSymbol_eq_jetSymbols (a : ℝ) (p : ℝ × ℤ) :
    cylinderSymbol a p.1 p.2.natAbs =
      cylinderJetSymbol [0, 0] p - (2 * (a : ℂ)) * cylinderJetSymbol [0] p +
        (a : ℂ) ^ 2 * cylinderJetSymbol [] p + cylinderJetSymbol [1, 1] p := by
  have hn : (p.2.natAbs : ℂ) ^ 2 = ((p.2 : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast (show (p.2.natAbs : ℝ) ^ 2 = (p.2 : ℝ) ^ 2 by
      simp [Nat.cast_natAbs])
  simp only [cylinderSymbol, cylinderJetSymbol, cylinderDerivativeSymbol, hn]
  norm_num only [Fin.isValue, ite_true, ite_false, one_ne_zero, mul_one]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- An actual spectral equation gives the forcing for the same finite inverse entries.
This is an equation of candidates, not a weak differential equation. -/
theorem cylinderInverseJetEntries_equation {a : ℝ} {H : ℝ × ℤ → ℂ}
    (hH : AEStronglyMeasurable H cylinderFourierMeasure)
    (hWH : MemLp (fun p ↦ (cylinderSignedWeight p : ℂ) * H p) 2 cylinderFourierMeasure)
    {G : ℝ × AddCircle (2 * Real.pi) → ℂ} (hG : MemLp G 2 logCylinderMeasure)
    (hσ : (fun p ↦ cylinderSymbol a p.1 p.2.natAbs * H p) =ᵐ[cylinderFourierMeasure]
      cylinderFourierData hG) :
    (fun q ↦ cylinderInverseJetEntries hH hWH [0, 0] q -
      (2 * (a : ℂ)) * cylinderInverseJetEntries hH hWH [0] q +
      (a : ℂ) ^ 2 * cylinderInverseJetEntries hH hWH [] q +
      cylinderInverseJetEntries hH hWH [1, 1] q) =ᵐ[logCylinderMeasure] G := by
  let h0 := cylinderSpectralJet_memLp hH hWH (w := []) (by simp)
  let ht := cylinderSpectralJet_memLp hH hWH (w := [0]) (by simp)
  let htt := cylinderSpectralJet_memLp hH hWH (w := [0, 0]) (by simp)
  let haa := cylinderSpectralJet_memLp hH hWH (w := [1, 1]) (by simp)
  let k0 := h0.toLp (cylinderSpectralJet [] H)
  let kt := ht.toLp (cylinderSpectralJet [0] H)
  let ktt := htt.toLp (cylinderSpectralJet [0, 0] H)
  let kaa := haa.toLp (cylinderSpectralJet [1, 1] H)
  let b := ktt - (2 * (a : ℂ)) • kt + ((a : ℂ) ^ 2) • k0 + kaa
  have hb : b = (cylinderFourierData_memLp hG).toLp (cylinderFourierData hG) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (ktt - (2 * (a : ℂ)) • kt + ((a : ℂ) ^ 2) • k0) kaa,
      Lp.coeFn_add (ktt - (2 * (a : ℂ)) • kt) (((a : ℂ) ^ 2) • k0),
      Lp.coeFn_sub ktt ((2 * (a : ℂ)) • kt), Lp.coeFn_smul (2 * (a : ℂ)) kt,
      Lp.coeFn_smul ((a : ℂ) ^ 2) k0, h0.coeFn_toLp, ht.coeFn_toLp,
      htt.coeFn_toLp, haa.coeFn_toLp, hσ, (cylinderFourierData_memLp hG).coeFn_toLp]
        with p ha1 ha2 hs hc1 hc2 hk0 hkt hktt hkaa hp hd
    dsimp only [b]
    rw [ha1, Pi.add_apply, ha2, Pi.add_apply, hs, Pi.sub_apply, hc1, hc2,
      Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [show k0 p = cylinderSpectralJet [] H p from hk0,
      show kt p = cylinderSpectralJet [0] H p from hkt,
      show ktt p = cylinderSpectralJet [0, 0] H p from hktt,
      show kaa p = cylinderSpectralJet [1, 1] H p from hkaa, hd, ← hp,
      cylinderSymbol_eq_jetSymbols]
    dsimp only [cylinderSpectralJet]
    ring
  have hi : cylinderInverseL2 b = cylinderInverseL2 ktt -
      (2 * (a : ℂ)) • cylinderInverseL2 kt +
      ((a : ℂ) ^ 2) • cylinderInverseL2 k0 + cylinderInverseL2 kaa := by
    simp only [b, map_add, map_sub, map_smul]
  have hg : (cylinderInverseL2 b : ℝ × AddCircle (2 * Real.pi) → ℂ) =ᵐ[logCylinderMeasure] G := by
    rw [hb]
    exact cylinderInverseL2_fourierData_ae hG
  filter_upwards [hg,
    cylinderInverseJetEntries_ae hH hWH (w := []) (by simp),
    cylinderInverseJetEntries_ae hH hWH (w := [0]) (by simp),
    cylinderInverseJetEntries_ae hH hWH (w := [0, 0]) (by simp),
    cylinderInverseJetEntries_ae hH hWH (w := [1, 1]) (by simp),
    Lp.coeFn_add (cylinderInverseL2 ktt - (2 * (a : ℂ)) • cylinderInverseL2 kt +
      ((a : ℂ) ^ 2) • cylinderInverseL2 k0) (cylinderInverseL2 kaa),
    Lp.coeFn_add (cylinderInverseL2 ktt - (2 * (a : ℂ)) • cylinderInverseL2 kt)
      (((a : ℂ) ^ 2) • cylinderInverseL2 k0),
    Lp.coeFn_sub (cylinderInverseL2 ktt) ((2 * (a : ℂ)) • cylinderInverseL2 kt),
    Lp.coeFn_smul (2 * (a : ℂ)) (cylinderInverseL2 kt),
    Lp.coeFn_smul ((a : ℂ) ^ 2) (cylinderInverseL2 k0)]
      with q hg hq0 hqt hqtt hqaa ha1 ha2 hs hc1 hc2
  rw [hq0, hqt, hqtt, hqaa]
  rw [hi, ha1, Pi.add_apply, ha2, Pi.add_apply, hs, Pi.sub_apply, hc1, hc2,
    Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at hg
  exact hg

end NoEmbeddedEigenvalues
