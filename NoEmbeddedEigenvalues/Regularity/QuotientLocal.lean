import NoEmbeddedEigenvalues.EigenfunctionTransport
import NoEmbeddedEigenvalues.TraceL2
import NoEmbeddedEigenvalues.LocalJets
import NoEmbeddedEigenvalues.WeightedTransport
import NoEmbeddedEigenvalues.FirstTransportGain
import NoEmbeddedEigenvalues.SecondTransportGain
import NoEmbeddedEigenvalues.WeakPointRemoval
import NoEmbeddedEigenvalues.LocalContinuousRepresentative

/-!
# Local analytic interfaces for the quotient construction

Weak derivative jets specify derivatives rather than differentiating arbitrary Sobolev
representatives. Radial integrability is stated separately from energies, so a default
Bochner integral cannot stand in for a divergent norm. The radius is Euclidean: the
usual metric on a product of real normed spaces uses the maximum norm.

All division identities and parity hypotheses are a.e. identities on their domains.
The derivative jets in point removal are only required on the punctured disk.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set Filter
open scoped Topology

/-- One-coordinate H³ division, including the uniform H² bound (`lem:odd-h3-division`). -/
theorem odd_h3_division {l r b : ℝ} (hlr : l < r) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ),
      MemSobolevOn 3 (axisRectangle 1 b l r) R →
      HasWeakJetOn 3 (axisRectangle 1 b l r) R D →
      (∀ᵐ p ∂(volume.restrict (axisRectangle 1 b l r)), R (axisReflect 1 p) = -R p) →
      ∃ (V : ℝ × ℝ → ℂ) (E : List (Fin 2) → ℝ × ℝ → ℂ),
        MemSobolevOn 2 (axisRectangle 1 b l r) V ∧
        HasWeakJetOn 2 (axisRectangle 1 b l r) V E ∧
        (∀ᵐ p ∂(volume.restrict (axisRectangle 1 b l r)), R p = (p.2 : ℂ) * V p) ∧
        (∀ᵐ p ∂(volume.restrict (axisRectangle 1 b l r)), V (axisReflect 1 p) = V p) ∧
        weakJetEnergy 2 (axisRectangle 1 b l r) E ≤
          C * weakJetEnergy 3 (axisRectangle 1 b l r) D := by
  sorry

/-- Weighted double division (`lem:weighted-double-division`), in squared-energy form.
No fourth derivative and no weighted order-zero hypothesis on R is imposed. -/
theorem weighted_double_division {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ),
      MemSobolevOn 3 (localDisk 0 ρ) R → HasWeakJetOn 3 (localDisk 0 ρ) R D →
      (∀ j, ∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), R (axisReflect j p) = -R p) →
      RadialJetLp 1 3 (localDisk 0 ρ) 0 D →
      RadialJetLp 2 2 (localDisk 0 ρ) 0 D →
      RadialJetLp 3 1 (localDisk 0 ρ) 0 D →
      ∃ (V : ℝ × ℝ → ℂ) (E : List (Fin 2) → ℝ × ℝ → ℂ),
        MemSobolevLocOn 2 (localDisk 0 ρ \ {0}) V ∧
        HasWeakJetOn 2 (localDisk 0 ρ \ {0}) V E ∧
        (∀ᵐ p ∂(volume.restrict (localDisk 0 ρ)), R p = ((p.1 * p.2 : ℝ) : ℂ) * V p) ∧
        RadialJetLp 0 2 (localDisk 0 ρ) 0 E ∧
        RadialJetLp 1 1 (localDisk 0 ρ) 0 E ∧
        RadialJetLp 2 0 (localDisk 0 ρ) 0 E ∧
        radialJetEnergy 0 2 (localDisk 0 ρ) 0 E +
          radialJetEnergy 1 1 (localDisk 0 ρ) 0 E +
          radialJetEnergy 2 0 (localDisk 0 ρ) 0 E ≤
          C * (radialJetEnergy 1 3 (localDisk 0 ρ) 0 D +
            radialJetEnergy 2 2 (localDisk 0 ρ) 0 D +
            radialJetEnergy 3 1 (localDisk 0 ρ) 0 D) := by
  sorry

/-- A nonzero continuous value at the center would force the weighted squared
mass in a square of side `2 * r` to grow at least as fast as `r⁻²`. -/
private theorem eq_zero_of_memLp_div_radius_sq {ρ : ℝ} (hρ : 0 < ρ)
    {g : ℝ × ℝ → ℂ} (hg : ContinuousOn g (localDisk 0 ρ))
    (hw : MemLp (fun p ↦ g p / (localRadius 0 p ^ 2 : ℂ)) 2
      (volume.restrict (localDisk 0 ρ))) : g 0 = 0 := by
  by_contra hn
  let c := ‖g 0‖ / 2
  have hc : 0 < c := half_pos (norm_pos_iff.mpr hn)
  have ho := isOpen_localDisk 0 ρ
  have hz : (0 : ℝ × ℝ) ∈ localDisk 0 ρ := by simpa [localDisk, localRadius] using hρ
  have hlarge : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ), c < ‖g p‖ :=
    ((hg.continuousAt (ho.mem_nhds hz)).norm.tendsto.eventually
      (lt_mem_nhds (by dsimp [c]; linarith [norm_pos_iff.mpr hn])))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (ho.mem_nhds hz) hlarge)
  let W := fun p ↦ ‖g p / (localRadius 0 p ^ 2 : ℂ)‖ ^ 2
  have hW : IntegrableOn W (localDisk 0 ρ) := hw.integrable_norm_pow (by norm_num)
  let M := ∫ p in localDisk 0 ρ, W p
  have hbound (r : ℝ) (hr : 0 < r) (hrδ : r < δ) :
      c ^ 2 ≤ (2 * r) ^ 2 * M := by
    let B := Metric.ball (0 : ℝ × ℝ) r
    have hBδ : B ⊆ Metric.ball (0 : ℝ × ℝ) δ := Metric.ball_subset_ball hrδ.le
    have hB : B ⊆ localDisk 0 ρ := fun p hp ↦ (hball (hBδ hp)).1
    have hvol : volume B = ENNReal.ofReal (2 * r) * ENNReal.ofReal (2 * r) := by
      change volume (Metric.ball ((0 : ℝ), (0 : ℝ)) r) = _
      rw [← ball_prod_same, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_ball]
    have hfinite : volume B ≠ ⊤ := by rw [hvol]; finiteness
    have hne : ∀ᵐ p ∂(volume.restrict B), p ≠ (0 : ℝ × ℝ) :=
      ae_restrict_of_ae (by rw [ae_iff]; simp [Measure.volume_eq_prod])
    have hle : ∀ᵐ p ∂(volume.restrict B), c ^ 2 ≤ (2 * r) ^ 4 * W p := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet, hne] with p hp hpne
      have hrad : localRadius 0 p ≤ 2 * r :=
        (localRadius_le_two_dist 0 p).trans (by linarith [Metric.mem_ball.mp hp])
      have hp0 := localRadius_ne_zero hpne
      have he : ‖g p‖ ^ 2 = localRadius 0 p ^ 4 * W p := by
        dsimp [W]
        rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ localRadius 0 p from Real.sqrt_nonneg _)]
        field_simp
      calc
        c ^ 2 ≤ ‖g p‖ ^ 2 :=
          pow_le_pow_left₀ hc.le (hball (hBδ hp)).2.le 2
        _ = localRadius 0 p ^ 4 * W p := he
        _ ≤ (2 * r) ^ 4 * W p := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (Real.sqrt_nonneg _) hrad 4) (sq_nonneg _)
    have hi := integral_mono_ae (integrableOn_const (C := c ^ 2) hfinite)
      ((hW.mono_set hB).const_mul ((2 * r) ^ 4)) hle
    rw [integral_const, Measure.real, Measure.restrict_apply_univ, hvol, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * r), smul_eq_mul, integral_const_mul] at hi
    have hmono : (∫ p in B, W p) ≤ M := integral_mono_measure
      (Measure.restrict_mono hB le_rfl) (Eventually.of_forall fun p ↦ sq_nonneg _) hW
    apply le_of_mul_le_mul_left _ (show 0 < (2 * r) ^ 2 by positivity)
    calc
      _ = (2 * r * (2 * r)) * c ^ 2 := by ring
      _ ≤ (2 * r) ^ 4 * (∫ p in B, W p) := hi
      _ ≤ (2 * r) ^ 4 * M := mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = (2 * r) ^ 2 * ((2 * r) ^ 2 * M) := by ring
  have hlim : Tendsto (fun r : ℝ ↦ (2 * r) ^ 2 * M) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun r : ℝ ↦ (2 * r) ^ 2 * M) := by fun_prop
    have ht := (hcont.continuousWithinAt (s := Ioi 0) (x := 0)).tendsto
    simpa using ht
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r ∈ Ioo 0 δ := Ioo_mem_nhdsGT hδ
  exact (not_le_of_gt (sq_pos_of_pos hc)) (ge_of_tendsto hlim
    (hsmall.mono fun r hr ↦ hbound r hr.1 hr.2))

/-- Weighted removal of a point, with a genuine continuous representative
(`lem:weighted-h2-point-removal`). No assigned raw value at zero is used.
The specified jet and full-disk bounds already imply the local regularity
assumed on the punctured disk. -/
theorem weighted_h2_point_removal {ρ : ℝ} (hρ : 0 < ρ) {V : ℝ × ℝ → ℂ}
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (_hV : MemSobolevLocOn 2 (localDisk 0 ρ \ {0}) V)
    (hD : HasWeakJetOn 2 (localDisk 0 ρ \ {0}) V D)
    (h0 : RadialJetLp 0 2 (localDisk 0 ρ) 0 D)
    (h1 : RadialJetLp 1 1 (localDisk 0 ρ) 0 D)
    (h2 : RadialJetLp 2 0 (localDisk 0 ρ) 0 D) :
    MemSobolevOn 2 (localDisk 0 ρ) V ∧
      ∃ g : ℝ × ℝ → ℂ, ContinuousOn g (localDisk 0 ρ) ∧ g 0 = 0 ∧
        V =ᵐ[volume.restrict (localDisk 0 ρ)] g := by
  have hv : MemLp V 2 (volume.restrict (localDisk 0 ρ)) := by
    rw [← hD.1]
    exact memLp_of_div_localRadius_pow (h0 [] rfl)
  have hfirst (j : Fin 2) : MemLp (D [j]) 2 (volume.restrict (localDisk 0 ρ)) :=
    memLp_of_div_localRadius_pow (h1 [j] rfl)
  have hsecond (i j : Fin 2) : MemLp (D [i, j]) 2 (volume.restrict (localDisk 0 ρ)) := by
    simpa using h2 [i, j] rfl
  have hloc {F : ℝ × ℝ → ℂ} (hF : MemLp F 2 (volume.restrict (localDisk 0 ρ))) :
      LocallyIntegrableOn F (localDisk 0 ρ) :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hF.locallyIntegrable (by norm_num))
  have htwo : MemSobolevOn 2 (localDisk 0 ρ) V := by
    refine ⟨hv, fun j ↦ ⟨D [j], ?_, hfirst j, fun i ↦ ⟨D [i, j], ?_, hsecond i j⟩⟩⟩
    · have hd := hD.2 [] (by decide) j
      rw [hD.1] at hd
      exact hd.remove_point (hloc hv) (hloc (hfirst j))
    · exact (hD.2 [j] (by simp) i).remove_point (hloc (hfirst j)) (hloc (hsecond i j))
  obtain ⟨g, hg, he⟩ := exists_continuousOn_rep_of_memSobolevLocOn_two
    (isOpen_localDisk 0 ρ) htwo.memSobolevLocOn
  refine ⟨htwo, g, hg, eq_zero_of_memLp_div_radius_sq hρ hg ?_, he⟩
  apply (h0 [] rfl).ae_eq
  filter_upwards [he] with p hp
  rw [hD.1, hp]

/-- Coordinate Hardy for either axis, using specified weak derivatives
(`lem:even-h2-axis-hardy`). -/
theorem even_h2_axis_hardy {j : Fin 2} {a l r : ℝ} (ha : 0 < a) (hlr : l < r)
    {F d dd : ℝ × ℝ → ℂ} (hF : MemSobolevOn 2 (axisRectangle j a l r) F)
    (he : ∀ᵐ p ∂(volume.restrict (axisRectangle j a l r)), F (axisReflect j p) = F p)
    (hd : HasWeakPartialOn (axisRectangle j a l r) j F d)
    (hdd : HasWeakPartialOn (axisRectangle j a l r) j d dd) :
    MemLp (fun p ↦ d p / (axisCoord j p : ℂ)) 2 (volume.restrict (axisRectangle j a l r)) ∧
      (∫ p in axisRectangle j a l r, ‖d p / (axisCoord j p : ℂ)‖ ^ 2) ≤
        4 * ∫ p in axisRectangle j a l r, ‖dd p‖ ^ 2 := by
  sorry

/-- Interior elliptic H³ regularity, with the Laplacian identified weakly
(the regularity part of `lem:elliptic-local`). -/
theorem elliptic_local_h3 {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u F : ℝ × ℝ → ℂ}
    {D : List (Fin 2) → ℝ × ℝ → ℂ} (hu : MemSobolevLocOn 2 U u)
    (hF : MemSobolevLocOn 1 U F) (hD : HasWeakJetOn 2 U u D)
    (hΔ : ∀ᵐ p ∂(volume.restrict U), D [0, 0] p + D [1, 1] p = F p) :
    MemSobolevLocOn 3 U u := by
  sorry

/-- Uniform squared dyadic elliptic estimate (`lem:elliptic-dyadic`). -/
theorem elliptic_dyadic : ∃ C : ℝ, 0 < C ∧ ∀ (c : ℝ × ℝ) (r : ℝ), 0 < r →
    ∀ (u F : ℝ × ℝ → ℂ) (D G : List (Fin 2) → ℝ × ℝ → ℂ),
      let A := {p | r < localRadius c p ∧ localRadius c p < 2 * r}
      let B := {p | r / 2 < localRadius c p ∧ localRadius c p < 4 * r}
      MemSobolevOn 2 B u → MemSobolevOn 1 B F →
      HasWeakJetOn 3 B u D → HasWeakJetOn 1 B F G →
      (∀ᵐ p ∂(volume.restrict B), D [0, 0] p + D [1, 1] p = F p) →
      RadialJetLp 3 0 A c D ∧
        radialJetEnergy 3 0 A c D ≤ C * (radialJetEnergy 1 0 B c G +
          r⁻¹ ^ 2 * radialJetEnergy 0 0 B c G + r⁻¹ ^ 6 * radialJetEnergy 0 0 B c D) := by
  sorry


end NoEmbeddedEigenvalues
