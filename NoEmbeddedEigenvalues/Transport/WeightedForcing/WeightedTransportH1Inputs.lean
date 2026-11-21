import NoEmbeddedEigenvalues.Transport.WeightedForcing.EndpointTangentialTrace
import NoEmbeddedEigenvalues.Transport.WeightedForcing.WeightedNumeratorSecondNorm
import NoEmbeddedEigenvalues.Transport.WeightedForcing.WeightedNumeratorH2
import NoEmbeddedEigenvalues.Transport.WeightedGains.PhaseCellDivision
import NoEmbeddedEigenvalues.Transport.WeightedForcing.WeightedTransportH1Data
import NoEmbeddedEigenvalues.Transport.WeightedForcing.WeightedCharacterQuarterDerivatives
import NoEmbeddedEigenvalues.Transport.WeightedForcing.WeightedQuarterPhysicalH1

/-!
# Ordinary weighted transport H¹: scalar and spatial interfaces

Blueprint: `def:quarter-h1-scalar-data`, `def:weighted-quarter-derivative-data`,
`lem:weighted-quarter-data-algebra`, `lem:weighted-numerator-second-norm`,
`lem:quarter-h1-scalar-data`,
`lem:weighted-character-quarter-derivatives`, `lem:transport-quarter-h1-gluing`.

Scalar data retain the original continuous full and half numerators. The quotient
has a canonical zero trace, not a prescribed raw endpoint value. Spatial data are
weak derivatives of the original raw recentered profiles, with physical-distance
weights and coordinate-area measure. Gluing uses the global weak transport
identity across the interior quarter seams, not the fact that those seams are null.
The ordinary route does not assume the stronger logarithmic numerator package,
whole-edge zero trace or an elliptic relation.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

private theorem restrict_interval_h1 {b c : ℝ} {F G : ℝ → ℂ}
    (h : HasIntervalH1 0 b F G) (hcb : c ≤ b) : HasIntervalH1 0 c F G := by
  have hs : Ioo (0 : ℝ) c ⊆ Ioo 0 b := Ioo_subset_Ioo le_rfl hcb
  exact ⟨h.memLp_value.mono_measure (Measure.restrict_mono_set _ hs),
    h.memLp_derivative.mono_measure (Measure.restrict_mono_set _ hs),
    fun a d ha had hd ↦ h.locally_absolutelyContinuous a d ha had (hd.trans_le hcb),
    h.hasDerivAt_ae.mono fun x hx hxI ↦ hx (hs hxI)⟩

/-- First-order/local H² data and resonant cancellation turn a supplied second
norm into ordinary quotient and half-numerator H¹ data.
No stronger numerator package is invoked. -/
theorem IsTransportPair.quarter_h1_scalar_data_of_second_norm
    {lam : ℝ} {κ : ℂ} (hκ : κ ^ 4 = 1)
    {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare))
    (hDf : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare))
    (hvκ : HasQuarterCharacterOn κ cellSquare v)
    (hfκ : HasQuarterCharacterOn κ cellSquare f)
    {r : ℝ} (hr : 0 < r)
    (hsecond : MemLp (fun h : ℝ ↦ (h : ℂ) * deriv (deriv (quarterNumerator lam g)) h) 2
      (volume.restrict (Ioo 0 r))) :
    ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧ b < r ∧ HasQuarterH1ScalarData lam κ g b := by
  obtain ⟨s, hs, hsh, hBoth⟩ := hp.weighted_numerator_local_h2 hcell hg hfg hD hf hDf
  let c := min r s
  have hc : 0 < c := lt_min hr hs
  have hcs : c ≤ s := min_le_right _ _
  have hcr : c ≤ r := min_le_left _ _
  have hc1 : c < 1 := by linarith
  have hN : HasIntervalH2Loc 0 c (quarterNumerator lam g) (deriv (quarterNumerator lam g))
      (deriv (deriv (quarterNumerator lam g))) :=
    fun a b ha hab hb ↦ (hBoth lam).1 a b ha hab (hb.trans_le hcs)
  have hAnn : orbitAnnulus 0 c ⊆ cellSquare := fun p hp ↦ hp.1.1
  have hAnnU : orbitAnnulus 0 c ⊆ U := hAnn.trans (subset_closure.trans hcell)
  have hz := (numerator_zeros hκ hp hc hc1 hAnnU hg hfg
    (ae_restrict_of_ae_restrict_of_subset hAnn hvκ)
    (ae_restrict_of_ae_restrict_of_subset hAnn hfκ)).2
  have hfirst := (hBoth lam).2.1.memLp_derivative.mono_measure
    (Measure.restrict_mono_set _ (Ioo_subset_Ioo le_rfl hcs))
  have hsecondc := hsecond.mono_measure
    (Measure.restrict_mono_set _ (Ioo_subset_Ioo le_rfl hcr))
  obtain ⟨b, hb, hbc, _, Q, Q₁, hQ, hfac, hQh, hQzero⟩ :=
    phase_cell_division hp.ne_zero hκ hc hc1 hN hz hfirst hsecondc
  have hbs : b ≤ s := hbc.le.trans hcs
  exact ⟨b, hb, lt_of_le_of_lt hbs hsh, hbc.trans_le hcr,
    Q, Q₁, hQ, hfac, hQh, hQzero,
    restrict_interval_h1 (hBoth lam).2.2.1.with_deriv hbs⟩


end NoEmbeddedEigenvalues
