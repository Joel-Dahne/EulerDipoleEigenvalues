module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.DiagonalH1
public import EulerDipoleEigenvalues.Virial.OriginalDomain.CellPeriodization
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.TraceH2

/-!
# Bulk transport in the diagonal trace charts

Blueprint: `lem:diagonal-boundary-transport`.

The same specified Cartesian weak gradient yields both chart partials and
the diagonal-coordinate form of the transport equation. No boundary
derivative is taken here.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter

/-- In the chart with the tangential coordinate first, swapping the two
original diagonal variables reverses the sign of the transport operator. -/
theorem HasWeakL0On.diagonalTraceChart_partials {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {F R X Y : ℝ × ℝ → ℂ} (hL : HasWeakL0On U F R)
    (hx : HasWeakPartialOn U 0 F X) (hy : HasWeakPartialOn U 1 F Y)
    (hX : MemLp X 2 (volume.restrict U)) (hY : MemLp Y 2 (volume.restrict U)) (j : Fin 2) :
    let C := diagonalTraceChart j
    let Q := C ⁻¹' U
    ∃ A B : ℝ × ℝ → ℂ,
      HasWeakPartialOn Q 0 (F ∘ C) A ∧ HasWeakPartialOn Q 1 (F ∘ C) B ∧
      MemLp A 2 (volume.restrict Q) ∧ MemLp B 2 (volume.restrict Q) ∧
      ∀ᵐ q ∂(volume.restrict Q),
        (if j = 0 then (1 : ℂ) else -1) *
          ((Real.sin q.2 * Real.cos q.1 : ℝ) * A q -
            (Real.sin q.1 * Real.cos q.2 : ℝ) * B q) = R (C q) := by
  let P := fun p ↦ (Real.sin p.2 : ℂ) * X p - (Real.sin p.1 : ℂ) * Y p
  have he : P =ᵐ[volume.restrict U] R := (ae_restrict_iff' hU.measurableSet).2
    ((hx.hasWeakL0On hU hy).ae_eq hU hL)
  let C := diagonalTraceChart j
  have hpre : P ∘ C =ᵐ[volume.restrict (C ⁻¹' U)] R ∘ C :=
    (QuasiMeasurePreserving.restrict (quasiMeasurePreserving_diagonalTraceChart j)
      (mapsTo_preimage C U)).ae he
  let S := fun p ↦ X p + Y p
  let D := fun p ↦ X p - Y p
  have eq (q : ℝ × ℝ) : P (diagInv q) =
      (Real.sin q.1 * Real.cos q.2 : ℝ) * D (diagInv q) -
        (Real.sin q.2 * Real.cos q.1 : ℝ) * S (diagInv q) := by
    simp only [P, S, D, diagInv_apply, Real.sin_sub, Real.sin_add, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_sub]
    ring
  have h0 := hx.comp_diagInv_fst hU hy
  have h1 := hx.comp_diagInv_snd hU hy
  have hSL := memLp_comp_diagInv hU.measurableSet (hX.add hY)
  have hDL := memLp_comp_diagInv hU.measurableSet (hX.sub hY)
  dsimp only
  fin_cases j <;> simp only [Fin.reduceFinMk] at C ⊢
  · let W := diagInv ⁻¹' U
    have hW : IsOpen W := hU.preimage diagInv.continuous
    have hsw (q : ℝ × ℝ) : diagonalTraceChart 0 q = diagInv q.swap := by cases q; rfl
    have hC : diagonalTraceChart 0 = diagInv ∘ Prod.swap := funext hsw
    let E := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
    have hE : planeAffine E 0 = (Prod.swap : ℝ × ℝ → ℝ × ℝ) := by
      funext q
      simp [planeAffine_apply, E]
    have hm : MeasurePreserving (planeAffine E 0) volume volume := by
      rw [hE, Measure.volume_eq_prod]
      exact Measure.measurePreserving_swap
    let dd : Fin 2 → ℝ × ℝ → ℂ := ![S ∘ diagInv, D ∘ diagInv]
    have hdd (i : Fin 2) : HasWeakPartialOn W i (F ∘ diagInv) (dd i) := by
      fin_cases i
      · exact h0
      · exact h1
    have hx' : HasWeakPartialOn ((diagInv ∘ Prod.swap) ⁻¹' U) 0
        (F ∘ diagInv ∘ Prod.swap) (D ∘ diagInv ∘ Prod.swap) := by
      have hh := HasWeakPartialOn.comp_planeAffine E 0 hm hW hdd 0
      simpa [W, hE, E, dd, affineCoeff, planeDirection, axisCoord, Function.comp_def,
        Set.preimage_preimage] using hh
    rw [hC]
    refine ⟨D ∘ diagInv ∘ Prod.swap, S ∘ diagInv ∘ Prod.swap,
      hx', h0.comp_swap_fst hW,
      memLp_comp_swap hW.measurableSet hDL, memLp_comp_swap hW.measurableSet hSL, ?_⟩
    change P ∘ diagonalTraceChart 0 =ᵐ[_] R ∘ diagonalTraceChart 0 at hpre
    rw [hC] at hpre
    filter_upwards [hpre] with q hq
    simpa only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap, Fin.isValue, eq_self, ite_true,
      one_mul] using
      ((eq q.swap).symm.trans hq)
  · change P ∘ diagonalTraceChart 1 =ᵐ[_] R ∘ diagonalTraceChart 1 at hpre
    have hC : diagonalTraceChart 1 = diagInv := rfl
    rw [hC] at hpre ⊢
    refine ⟨S ∘ diagInv, D ∘ diagInv, h0, h1, hSL, hDL, ?_⟩
    filter_upwards [hpre] with q hq
    simpa only [Function.comp_apply, Fin.isValue, one_ne_zero, ite_false, neg_one_mul,
      neg_sub] using (eq q).symm.trans hq

end EulerDipoleEigenvalues
