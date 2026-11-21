import NoEmbeddedEigenvalues.Analysis.LocalSobolev.WeightedTraces
import NoEmbeddedEigenvalues.Analysis.Inequalities.ScalarDivision
import NoEmbeddedEigenvalues.Transport.PeriodicComparison.GoodWindows
import NoEmbeddedEigenvalues.Transport.WeightedGains.QuarterCoordinates
import NoEmbeddedEigenvalues.Transport.WeightedGains.WeightedNumeratorData
import NoEmbeddedEigenvalues.Transport.WeightedGains.ZeroSaddleTransportGain
import NoEmbeddedEigenvalues.Transport.WeightedForcing.WeightedTransportH1Assembly
import NoEmbeddedEigenvalues.Transport.WeightedForcing.EdgeCornerTransport

/-!
# Weighted cellwise transport regularity interfaces

The weak gradient of the forcing is specified, and weights use physical-area L².
Regularity and zero boundary trace are different conclusions. Only the latter uses
zero continuous forcing on the chosen whole edge and the critical one-sided trace bound.

Quarter profiles use independent recentered time coordinates. Their h/t derivatives
carry weights d and 1/d respectively; no unweighted global H¹ norm on the quarter
coordinate domain is asserted. The physical stream level is Ψ = 2h.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set

/-- Weighted forcing gives the second mass gain and cellwise physical H¹, together
with weak recentered quarter derivatives (`lem:weighted-transport-h1`). -/
theorem weighted_transport_h1 {lam : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hb : Bornology.IsBounded U)
    (hcell : closure cellSquare ⊆ U) {D : Fin 2 → ℝ × ℝ → ℂ}
    (hD : ∀ j, HasWeakPartialOn U j f (D j))
    (hf : MemLp (fun p ↦ f p / (saddleDist p ^ 2 : ℂ)) 2
      (volume.restrict cellSquare))
    (hDf : ∀ j, MemLp (fun p ↦ D j p / (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2
      (volume.restrict cellSquare)) :
    MemLp (fun p ↦ v p / (saddleDist p ^ 2 : ℂ)) 2 (volume.restrict cellSquare) ∧
      ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ < 1 / 2 ∧
        MemSobolevOn 1 (cellSeparatrixStrip (2 * h₀)) v ∧
        ∃ A B : Fin 4 → ℝ × ℝ → ℂ, ∀ k,
          HasWeakPartialOn (quarterOrbitStrip h₀) 0
            (fun q ↦ v (recenteredQuarterMap k q)) (A k) ∧
          HasWeakPartialOn (quarterOrbitStrip h₀) 1
            (fun q ↦ v (recenteredQuarterMap k q)) (B k) ∧
          MemLp (fun q ↦ (saddleDist (recenteredQuarterMap k q) : ℂ) * A k q) 2
            (volume.restrict (quarterOrbitStrip h₀)) ∧
          MemLp (fun q ↦ B k q / (saddleDist (recenteredQuarterMap k q) : ℂ)) 2
            (volume.restrict (quarterOrbitStrip h₀)) := by
  refine ⟨weighted_transport_second_mass hp hb hcell hD hf hDf, ?_⟩
  obtain ⟨b, hpos, hhalf, A, B, hAB⟩ :=
    weighted_transport_quarter_derivatives hp hb hcell hD hf hDf
  exact ⟨b, hpos, hhalf,
    hp.cell_h1_of_weighted_quarter_derivatives hcell hpos hhalf hAB, A, B, hAB⟩

/-- Zero forcing on one whole regular edge forces its canonical cellwise trace
of v to vanish (`lem:transport-zero-edge-trace`). H¹ and the mass weight are inputs,
not inferred merely from the zero forcing values. -/
theorem transport_zero_edge_trace {lam ε : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U) (hε : 0 < ε)
    (hv : MemSobolevOn 1 (cellSeparatrixStrip ε) v)
    (hw : MemLp (fun p ↦ v p / (saddleDist p : ℂ)) 2
      (volume.restrict (cellSeparatrixStrip ε)))
    {g : ℝ × ℝ → ℂ} (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    (j : Fin 2) (positive : Bool)
    (hzero : ∀ s ∈ Ioo (-Real.pi / 2) (Real.pi / 2),
      g (diagonalTraceChart j (s, cellEdgeNormal positive)) = 0) :
    HasCellEdgeTrace (cellSeparatrixStrip ε) j positive v (fun _ ↦ 0) := by
  let w := min (ε / 4) (Real.pi / 2)
  have hwpos : 0 < w := lt_min (by linarith) (by positivity)
  have hwε : 2 * w ≤ ε := by dsimp [w]; linarith [min_le_left (ε / 4) (Real.pi / 2)]
  have hwπ : w < Real.pi := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  obtain ⟨z, hz⟩ := common_edge_window_modulus hwpos (by
    intro a b hab hs
    apply hp.inward_edge_window_modulus hcell hv hg hfg j positive hzero hab hwpos hs
    intro q hq
    exact inwardEdgeChart_mem_collar ⟨hq.2.1, hq.2.2.trans hwπ⟩
      (show 2 * q.2 < ε from lt_of_lt_of_le (by linarith [hq.2.2]) hwε)
      (hs (Ioo_subset_Icc_self hq.1)) j positive)
  have hz0 := inward_edge_common_modulus_eq_zero hwpos hwε hwπ j positive hv hw hz
  intro l r a b hlr hab hreg hedge hrect
  obtain ⟨T, hT, hnorm⟩ := hz l r hlr hreg
  let C := diagonalTraceChart j
  let V := v ∘ C
  let t := cellEdgeNormal positive
  have hV := (hv.comp_diagonalTraceChart (isOpen_cellSeparatrixStrip ε) j).mono
    (image_subset_iff.mp hrect)
  obtain ⟨D, hd, hD⟩ := hV.2 1
  have ht : t ∈ Icc a b := by
    cases positive
    · change a = cellEdgeNormal false at hedge
      exact ⟨hedge.le, hedge.symm.le.trans hab.le⟩
    · change b = cellEdgeNormal true at hedge
      exact ⟨hab.le.trans hedge.le, hedge.symm.le⟩
  obtain ⟨S, hS⟩ := hd.exists_transverse_trace hlr hab ht hV.1 hD
  let δ := min w (b - a)
  have hδ : 0 < δ := lt_min hwpos (sub_pos.mpr hab)
  have hδw : δ ≤ w := min_le_left _ _
  have hδab : δ ≤ b - a := min_le_right _ _
  let φ := fun u ↦ edgeSideSign positive * (Real.pi / 2 - u)
  have hφ : MapsTo φ (Ioo 0 δ) (Ioo a b) := by
    intro u hu
    cases positive
    · change a = -Real.pi / 2 at hedge
      change -1 * (Real.pi / 2 - u) ∈ Ioo a b
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    · change b = Real.pi / 2 at hedge
      change 1 * (Real.pi / 2 - u) ∈ Ioo a b
      exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hm : MeasurePreserving φ volume volume := by
    cases positive
    · convert measurePreserving_add_right volume (-(Real.pi / 2)) using 1
      funext u
      simp [φ, edgeSideSign]
      ring
    · simpa [φ, edgeSideSign] using Measure.measurePreserving_sub_left volume (Real.pi / 2)
  have hφc : Continuous φ := by fun_prop
  have hφ0 : φ 0 = t := by
    cases positive <;> simp [φ, t, edgeSideSign, cellEdgeNormal, neg_div]
  have hEq := hT.ae_eq_inward hS hδ hδw (k := id) (fun _ hs ↦ hs) hφ
    (MeasurePreserving.id volume) hm hφc hφ0 (fun s _ u _ ↦ by
      change v (C (edgeInward positive (s, u))) = v (C (s, φ u))
      rw [edgeInward_apply])
  have hS0 : (fun _ ↦ (0 : ℂ)) =ᵐ[volume.restrict (Ioo l r)] S := by
    filter_upwards [hEq, hnorm] with s he hn
    change T s = S s at he
    have hTs : T s = 0 := norm_eq_zero.mp (by simpa [hz0] using hn)
    exact hTs.symm.trans he
  exact hS.congr_trace hS0

end NoEmbeddedEigenvalues
