import NoEmbeddedEigenvalues.OddOdd.WeightedVirial.OddOddVirial

/-!
# Even H² quotient gradient traces

Reconstruction through the Fourier Laplacian reduces the quadratic limits to
the even–even stream traces. The constant Fourier mode does not change the
gradient or arc derivatives. A bounded-value Cauchy–Schwarz estimate handles
the first-order term, retaining one exceptional set after rescaling Ψ = 2h.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter Topology

/-- A bounded continuous value paired with an L² normal gradient has vanishing
    first-order level flux whenever its normal energy tends to zero. -/
private theorem first_trace_limit (u dx dy : L2) {N : Set ℝ}
    (hn : Tendsto (fun h ↦ levelIntegral h (fun p ↦
      ‖ddInwardNormal (liftL2 dx) (liftL2 dy) p‖ ^ 2))
      (𝓝[Ioi 0 \ N] 0) (𝓝 0)) :
    ∃ B : Set ℝ, volume B = 0 ∧
      Tendsto (fun h ↦ levelIntegral h (fun p ↦ gradNorm p *
        ((starRingEnd ℂ) (continuousRep u (torusProj p)) *
          ddInwardNormal (liftL2 dx) (liftL2 dy) p).re))
        (𝓝[Ioi 0 \ (N ∪ B)] 0) (𝓝 0) := by
  let f := fun p ↦ continuousRep u (torusProj p)
  let n := ddInwardNormal (liftL2 dx) (liftL2 dy)
  let M := ‖continuousRep u‖
  have mf : Measurable f :=
    ((continuousRep u).continuous.comp isOpenQuotientMap_torusProj.continuous).measurable
  have ml (d : L2) : Measurable (liftL2 d) :=
    (Lp.stronglyMeasurable d).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable
  have mn : Measurable n := by
    have mx := ml dx
    have my := ml dy
    unfold n ddInwardNormal normalDeriv gradNorm
    fun_prop
  have hb : Bornology.IsBounded cellSquare :=
    isBounded_cellNeighbourhood.subset fun _ hp ↦
      closure_cellSquare_subset_cellNeighbourhood (subset_closure hp)
  have mi : MemLp n 2 (volume.restrict cellSquare) :=
    (memLp_normalDeriv (memLp_liftL2 dx hb) (memLp_liftL2 dy hb)).neg
  have hi : IntegrableOn (fun p ↦ ‖n p‖ ^ 2) cellSquare :=
    mi.integrable_norm_pow (by norm_num)
  let P := fun h ↦ IntegrableOn (fun t ↦ ‖n (dipoleOrbit h t)‖ ^ 2)
    (Ico (-2 * eighthPeriod h) (6 * eighthPeriod h))
  let B := {h | h ∈ Ioo (0 : ℝ) 1 ∧ ¬P h}
  have hB : volume B = 0 := by
    simpa only [B, P, ae_iff, not_imp] using
      (ae_restrict_iff' measurableSet_Ioo).mp (integral_cellSquare_eq hi).1
  have hmono : 𝓝[Ioi (0 : ℝ) \ (N ∪ B)] 0 ≤ 𝓝[Ioi 0 \ N] 0 :=
    nhdsWithin_mono _ (sdiff_subset_sdiff_right subset_union_left)
  obtain ⟨K, h₀, hh₀, hK⟩ := levelIntegral_gradNorm_sq_le
  have hup : Tendsto (fun h ↦ M * √(K * levelIntegral h (fun p ↦ ‖n p‖ ^ 2)))
      (𝓝[Ioi 0 \ (N ∪ B)] 0) (𝓝 0) := by
    simpa using ((hn.mono_left hmono).const_mul K).sqrt.const_mul M
  refine ⟨B, hB, squeeze_zero_norm' ?_ hup⟩
  have hsmall : ∀ᶠ h in 𝓝[Ioi (0 : ℝ) \ (N ∪ B)] 0, h ∈ Ioo 0 (min h₀ 1) :=
    nhdsWithin_mono _ sdiff_subset (Ioo_mem_nhdsGT (lt_min hh₀ one_pos))
  filter_upwards [hsmall, self_mem_nhdsWithin] with h hh hmem
  have hp : P h := by
    by_contra hbad
    exact hmem.2 (Or.inr ⟨⟨hh.1, hh.2.trans_le (min_le_right _ _)⟩, hbad⟩)
  have hbound := abs_levelIntegral_first_le_of_bounded mf mn (norm_nonneg _)
    hh.1 (hh.2.trans_le (min_le_right _ _))
    (hK h ⟨hh.1, hh.2.trans_le (min_le_left _ _)⟩
      (hh.2.trans_le (min_le_right _ _))) hp
    (Eventually.of_forall fun t ↦ (continuousRep u).norm_coe_le_norm _)
  have hre (z w : ℂ) : ((starRingEnd ℂ) z * w).re =
      (z * (starRingEnd ℂ) w).re := by simp [Complex.mul_re]
  simpa only [Real.norm_eq_abs, hre] using hbound

/-- Even H² gradient limits, using specified Fourier derivatives and continuous values.
    All three limits share one exceptional null set in the `ε = Ψ` variable. -/
theorem dd_quotient_gradient_traces {u dx dy : L2} (hu : MemSobolev 2 u)
    (hs : InSector true true u) (hx : HasFourierPartial 0 u dx)
    (hy : HasFourierPartial 1 u dy) :
    (∀ k : Fin 4, Integrable (fun t ↦ Real.cosh t ^ 2 / 2 *
      ‖deriv (ddArcTrace u k) t‖ ^ 2)) ∧
    ∃ N : Set ℝ, volume N = 0 ∧
      Tendsto (fun ε ↦ levelIntegral (ε / 2) (fun p ↦
        ‖ddInwardNormal (liftL2 dx) (liftL2 dy) p‖ ^ 2))
        (𝓝[Ioi 0 \ N] 0) (𝓝 0) ∧
      Tendsto (fun ε ↦ levelIntegral (ε / 2) (fun p ↦
        ‖tangentDeriv (liftL2 dx) (liftL2 dy) p‖ ^ 2))
        (𝓝[Ioi 0 \ N] 0) (𝓝 (∑ k : Fin 4,
          ∫ t, Real.cosh t ^ 2 / 2 * ‖deriv (ddArcTrace u k) t‖ ^ 2)) ∧
      Tendsto (fun ε ↦ levelIntegral (ε / 2) (fun p ↦ gradNorm p *
        ((starRingEnd ℂ) (continuousRep u (torusProj p)) *
          ddInwardNormal (liftL2 dx) (liftL2 dy) p).re))
        (𝓝[Ioi 0 \ N] 0) (𝓝 0) := by
  obtain ⟨v, hv⟩ := hu.exists_hasFourierLaplacian
  have he (j : Fin 2) (d : L2) (hd : HasFourierPartial j u d) :
      d = streamPartial j v := by
    apply fourierCoeff_ext
    intro k
    rw [hd k, hasFourierPartial_streamPartial v j k]
    by_cases hk : k = 0
    · subst k
      simp [frequencyComponent]
    · have hc : fourierCoeff (invLap v) k = fourierCoeff u k := by
        have hn : (normSq k : ℂ) ≠ 0 := by exact_mod_cast (normSq_pos k hk).ne'
        simp only [fourierCoeff_invLap, hk, ite_false, hv k]
        field_simp
      rw [hc]
  rw [he 0 dx hx, he 1 dy hy]
  obtain ⟨ha, N, hN, hn, ht, -⟩ := ee_gradient_traces (hs.even_laplacian hv)
  have hg (k : Fin 4) : ddArcTrace u k =
      fun t ↦ (contStream v ∘ cellArc (k : ℕ)) t + fourierCoeff u 0 :=
    funext fun t ↦ hv.continuousRep_eq hu _
  have hd (k : Fin 4) : deriv (ddArcTrace u k) =
      deriv (contStream v ∘ cellArc (k : ℕ)) := by
    rw [hg]
    funext t
    simp only [deriv_add_const]
  have harc (k : Fin 4) : Integrable (fun t ↦ Real.cosh t ^ 2 / 2 *
      ‖deriv (ddArcTrace u k) t‖ ^ 2) := by
    convert (ha (k : ℕ) k.isLt).const_mul (1 / 2 : ℝ) using 1
    funext t
    rw [hd]
    ring
  have hn' : Tendsto (fun h ↦ levelIntegral h (fun p ↦
      ‖ddInwardNormal (liftL2 (streamPartial 0 v)) (liftL2 (streamPartial 1 v)) p‖ ^ 2))
      (𝓝[Ioi 0 \ N] 0) (𝓝 0) := by
    simpa only [ddInwardNormal, norm_neg, streamNormal, streamLiftX, streamLiftY] using hn
  have ht' : Tendsto (fun h ↦ levelIntegral h (fun p ↦
      ‖tangentDeriv (liftL2 (streamPartial 0 v)) (liftL2 (streamPartial 1 v)) p‖ ^ 2))
      (𝓝[Ioi 0 \ N] 0) (𝓝 (∑ k : Fin 4,
        ∫ t, Real.cosh t ^ 2 / 2 * ‖deriv (ddArcTrace u k) t‖ ^ 2)) := by
    simpa only [← Fin.sum_univ_eq_sum_range, hd, streamTangent, streamLiftX, streamLiftY]
      using ht
  obtain ⟨B, hB, hm⟩ := first_trace_limit u (streamPartial 0 v) (streamPartial 1 v) hn'
  let Nh := N ∪ B
  let Neps := (fun ε : ℝ ↦ (1 / 2 : ℝ) * ε) ⁻¹' Nh
  have hNh : volume Nh = 0 := measure_union_null hN hB
  have hNeps : volume Neps = 0 := by
    dsimp only [Neps]
    rw [Real.volume_preimage_mul_left (by norm_num : (1 / 2 : ℝ) ≠ 0), hNh, mul_zero]
  have hmono : 𝓝[Ioi (0 : ℝ) \ Nh] 0 ≤ 𝓝[Ioi 0 \ N] 0 :=
    nhdsWithin_mono _ (sdiff_subset_sdiff_right subset_union_left)
  have hdiv : Tendsto (fun ε : ℝ ↦ ε / 2)
      (𝓝[Ioi 0 \ Neps] 0) (𝓝[Ioi 0 \ Nh] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using ((tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0)).mono_left
        nhdsWithin_le_nhds).div_const (2 : ℝ)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine ⟨show (0 : ℝ) < ε / 2 from div_pos hε.1 two_pos, ?_⟩
      have hne : (1 / 2 : ℝ) * ε ∉ Nh := hε.2
      simpa only [show (1 / 2 : ℝ) * ε = ε / 2 by ring] using hne
  exact ⟨harc, Neps, hNeps, (hn'.mono_left hmono).comp hdiv,
    (ht'.mono_left hmono).comp hdiv, hm.comp hdiv⟩

end NoEmbeddedEigenvalues
