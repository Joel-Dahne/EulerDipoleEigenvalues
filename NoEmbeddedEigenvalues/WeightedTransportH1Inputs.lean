import NoEmbeddedEigenvalues.EndpointTangentialTrace
import NoEmbeddedEigenvalues.WeightedNumeratorH2
import NoEmbeddedEigenvalues.PhaseCellDivision

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

/-- Ordinary scalar division data, without the logarithmic quantitative bundle. -/
def HasQuarterH1ScalarData (lam : ℝ) (κ : ℂ) (g : ℝ × ℝ → ℂ) (b : ℝ) : Prop :=
  ∃ Q Q₁ : ℝ → ℂ, HasIntervalH1 0 b Q Q₁ ∧
    (∀ h ∈ Ioo 0 b, quarterDivisor lam κ h * Q h = quarterNumerator lam g h) ∧
    MemLp (fun h ↦ Q h / (h : ℂ)) 2 (volume.restrict (Ioo 0 b)) ∧
    intervalH1Extension 0 b Q Q₁ 0 = 0 ∧
    HasIntervalH1 0 b (quarterHalfNumerator lam g) (deriv (quarterHalfNumerator lam g))

/-- Joint weak derivatives of the same raw field on all four recentered quarters. -/
def HasWeightedQuarterDerivatives (b : ℝ) (v : ℝ × ℝ → ℂ)
    (A B : Fin 4 → ℝ × ℝ → ℂ) : Prop :=
  ∀ k, HasWeakPartialOn (quarterOrbitStrip b) 0
      (fun q ↦ v (recenteredQuarterMap k q)) (A k) ∧
    HasWeakPartialOn (quarterOrbitStrip b) 1
      (fun q ↦ v (recenteredQuarterMap k q)) (B k) ∧
    MemLp (fun q ↦ (saddleDist (recenteredQuarterMap k q) : ℂ) * A k q) 2
      (volume.restrict (quarterOrbitStrip b)) ∧
    MemLp (fun q ↦ B k q / (saddleDist (recenteredQuarterMap k q) : ℂ)) 2
      (volume.restrict (quarterOrbitStrip b))

/-- Restriction keeps the same joint fields and their distance weights. -/
theorem HasWeightedQuarterDerivatives.mono {b c : ℝ} {v : ℝ × ℝ → ℂ}
    {A B : Fin 4 → ℝ × ℝ → ℂ} (h : HasWeightedQuarterDerivatives b v A B)
    (hcb : c ≤ b) : HasWeightedQuarterDerivatives c v A B := by
  have hs : quarterOrbitStrip c ⊆ quarterOrbitStrip b :=
    fun q hq ↦ ⟨hq.1, hq.2.1.trans_le hcb, hq.2.2⟩
  exact fun k ↦ ⟨(h k).1.mono hs, (h k).2.1.mono hs,
    (h k).2.2.1.mono_measure (Measure.restrict_mono_set _ hs),
    (h k).2.2.2.mono_measure (Measure.restrict_mono_set _ hs)⟩

/-- Finite sums preserve actual weak derivatives and both genuine L² norms. -/
theorem HasWeightedQuarterDerivatives.add {b : ℝ} {v w : ℝ × ℝ → ℂ}
    {A B C E : Fin 4 → ℝ × ℝ → ℂ}
    (h : HasWeightedQuarterDerivatives b v A B)
    (h' : HasWeightedQuarterDerivatives b w C E) :
    HasWeightedQuarterDerivatives b (v + w) (A + C) (B + E) := by
  intro k
  refine ⟨(h k).1.add (h' k).1, (h k).2.1.add (h' k).2.1, ?_, ?_⟩
  · apply ((h k).2.2.1.add (h' k).2.2.1).ae_eq
    exact Eventually.of_forall fun q ↦ by
      dsimp only [Pi.add_apply]
      ring
  · apply ((h k).2.2.2.add (h' k).2.2.2).ae_eq
    exact Eventually.of_forall fun q ↦ (add_div _ _ _).symm

private theorem restrict_interval_h1 {b c : ℝ} {F G : ℝ → ℂ}
    (h : HasIntervalH1 0 b F G) (hcb : c ≤ b) : HasIntervalH1 0 c F G := by
  have hs : Ioo (0 : ℝ) c ⊆ Ioo 0 b := Ioo_subset_Ioo le_rfl hcb
  exact ⟨h.memLp_value.mono_measure (Measure.restrict_mono_set _ hs),
    h.memLp_derivative.mono_measure (Measure.restrict_mono_set _ hs),
    fun a d ha had hd ↦ h.locally_absolutelyContinuous a d ha had (hd.trans_le hcb),
    h.hasDerivAt_ae.mono fun x hx hxI ↦ hx (hs hxI)⟩

/-- Global control of the actual ordinary second numerator derivative under the
original weighted forcing inputs (`lem:weighted-numerator-second-norm`).
This is the ordinary scalar derivative, not only the fixed-time bulk term. -/
theorem IsTransportPair.weighted_numerator_second_norm
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare))
    (hDf : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧ ∀ μ : ℝ,
      MemLp (fun h : ℝ ↦ (h : ℂ) * deriv (deriv (quarterNumerator μ g)) h) 2
        (volume.restrict (Ioo 0 r)) := by
  sorry

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

/-- Reconstruct one character's raw weak profiles on all recentered quarters
from ordinary scalar data. This includes the weighted level and time estimates,
not spatial seam gluing (`lem:weighted-character-quarter-derivatives`). -/
theorem IsTransportPair.weighted_character_quarter_derivatives
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
    {r : ℝ} (hr : 0 < r) (hrh : r < 1 / 2) (hscalar : HasQuarterH1ScalarData lam κ g r) :
    ∃ b : ℝ, 0 < b ∧ b < r ∧ ∃ A B : Fin 4 → ℝ × ℝ → ℂ,
      HasWeightedQuarterDerivatives b v A B := by
  sorry

/-- Physical inverse-frame reconstruction and no-jump gluing at the interior
quarter rays. The weak transport identity supplies seam compatibility; no zero
forcing/trace or elliptic hypothesis is added (`lem:transport-quarter-h1-gluing`). -/
theorem IsTransportPair.cell_h1_of_weighted_quarter_derivatives
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    {b : ℝ} (hb : 0 < b) (hbh : b < 1 / 2)
    {A B : Fin 4 → ℝ × ℝ → ℂ} (hAB : HasWeightedQuarterDerivatives b v A B) :
    MemSobolevOn 1 (cellSeparatrixStrip (2 * b)) v := by
  sorry

end NoEmbeddedEigenvalues
