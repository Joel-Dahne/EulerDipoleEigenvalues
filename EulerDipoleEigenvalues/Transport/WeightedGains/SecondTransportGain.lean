module

public import EulerDipoleEigenvalues.Transport.WeightedGains.WeightedQuarterProjections
public import EulerDipoleEigenvalues.Transport.WeightedGains.SubcriticalCellMass

/-!
# Second transport gain

Blueprint: `lem:transport-second-gain`.

Restrict to a rotation-invariant neighbourhood and project both original raw
fields and the supplied continuous forcing. The original weak gradient gives
the projected gradients by Cartesian rotation and finite linearity, retaining
their weighted cell norms. Each of the four characters has full-cell second
mass, so pointwise recombination does not require a common collar.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

/-- Second transport gain (`lem:transport-second-gain`), with an actual continuous
forcing representative and weak derivatives rather than pointwise derivatives. -/
theorem transport_second_gain {lam δ : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hb : Bornology.IsBounded U)
    (hcell : closure cellSquare ⊆ U) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {g : ℝ × ℝ → ℂ} (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (hbound : ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ p ∈ cellSquare,
      saddleDist p < ε → ‖g p‖ ≤ C * Real.rpow (saddleDist p) (2 - δ))
    {D : Fin 2 → ℝ × ℝ → ℂ}
    (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hw : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (2 - δ) : ℂ)) 2
      (volume.restrict cellSquare)) :
    MemLp (fun p ↦ v p / ((saddleDist p) ^ 2 : ℂ)) 2
      (volume.restrict cellSquare) := by
  have hs : 0 < 2 - δ := by linarith
  obtain ⟨K, hK, hglobal⟩ := exists_cell_forcing_rpow_bound hb hcell hg hs hbound
  obtain ⟨V, hV, hbV, hVU, hcellV, hRV⟩ :=
    exists_rotationInvariant_transport_neighbourhood hp.isOrbitUnion hb hcell
  have hpV := hp.mono hV hVU
  have hgV := hg.mono hVU
  have hfgV := ae_restrict_of_ae_restrict_of_subset hVU hfg
  have hDV (j : Fin 2) := (hD j).mono hVU
  have hchar (κ : ℂ) (hκ : κ ^ 4 = 1) :
      MemLp (fun p ↦ quarterCharacterProjection κ v p / ((saddleDist p) ^ 2 : ℂ)) 2
        (volume.restrict cellSquare) := by
    obtain ⟨E, hE⟩ := exists_weightedGradient_quarterCharacterProjection hV.1 hRV hDV hw κ
    have hκnorm : ‖κ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hκ (by decide)
    have hgrowth : ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ p ∈ cellSquare,
        saddleDist p < ε → ‖quarterCharacterProjection κ g p‖ ≤
          C * Real.rpow (saddleDist p) (2 - δ) :=
      ⟨K, 1, hK, by norm_num,
        fun p hp _ ↦ quarterCharacterProjection_rpow_bound hκnorm hglobal p hp⟩
    apply (hpV.quarterCharacterProjection hRV κ).subcritical_character_memLp
      hκ hbV hcellV hδ0 hδ1 (continuousOn_quarterCharacterProjection hgV hRV κ)
      (quarterCharacterProjection_congr_ae hV.1.measurableSet hRV hfgV κ)
      hgrowth (fun j ↦ (hE j).1) (fun j ↦ (hE j).2)
      (r := 1 / 2) (by norm_num)
    · exact Eventually.of_forall (quarterCharacterProjection_rotLift hκ v)
    · exact Eventually.of_forall (quarterCharacterProjection_rotLift hκ f)
  have hsum := (((hchar 1 (by norm_num)).add (hchar (-1) (by norm_num))).add
    (hchar Complex.I (by norm_num))).add (hchar (-Complex.I) (by
      calc (-Complex.I) ^ 4 = Complex.I ^ 4 := by ring
           _ = 1 := by norm_num))
  apply hsum.ae_eq
  exact Eventually.of_forall fun p ↦ by
    simp only [Pi.add_apply, ← add_div, quarterCharacterProjection_sum]


end EulerDipoleEigenvalues
