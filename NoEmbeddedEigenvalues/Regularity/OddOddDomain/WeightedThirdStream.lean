import NoEmbeddedEigenvalues.Regularity.OddOddSeparatrix.OddOddRegularity

/-! # Weighted third derivatives of the stream remainders -/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set

/-- Weighted third derivatives of both quadratic and dipole remainders
(`lem:dd-weighted-third-stream`), using the same normalized coefficient a. -/
theorem dd_weighted_third_stream {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω) :
    ∀ c ∈ saddleSet, ∃ ρ : ℝ, 0 < ρ ∧ ∃ a : ℂ,
      ∃ D₀ D : List (Fin 2) → ℝ × ℝ → ℂ,
        HasWeakJetOn 3 (localDisk c ρ) (fun p ↦ contStream ω p - saddleQuadratic c a p) D₀ ∧
        HasWeakJetOn 3 (localDisk c ρ) (fun p ↦ contStream ω p - a * (dipoleLift p : ℂ)) D ∧
        (∀ k ≤ 3, RadialJetLp k (4 - k) (localDisk c ρ) c D₀) ∧
        (∀ k ≤ 3, RadialJetLp k (4 - k) (localDisk c ρ) c D) := by
  intro c hc
  obtain ⟨_, hjet⟩ := saddle_dd hlam hω hs
  obtain ⟨ρ₀, hρ₀, a, ha, _⟩ := hjet c hc
  obtain ⟨D₀, hD₀, hw₀⟩ := ha
  obtain ⟨ρT, hρT, T, hT, hwT⟩ := saddle_taylor_correction hc a
  obtain ⟨U, hU, hsep, G, hG⟩ := dd_weighted_gradient hlam hω hs
  have hcU : c ∈ U := by
    apply hsep
    have h := saddle_dipole_factorization hc (0, 0)
    simpa [saddleOrthoChart] using h
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU c hcU
  let V := Metric.ball c (ε / 2)
  have hVc : IsCompact (closure V) :=
    (isCompact_closedBall c (ε / 2)).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  have hVU : closure V ⊆ U := by
    intro p hp
    apply hεU
    have hd := Metric.closure_ball_subset_closedBall hp
    change dist p c ≤ ε / 2 at hd
    change dist p c < ε
    linarith
  let r := min ρ₀ (min ρT (ε / 2))
  have hr : 0 < r := lt_min hρ₀ (lt_min hρT (by positivity))
  have hr₀ : r ≤ ρ₀ := min_le_left _ _
  have hrT : r ≤ ρT := (min_le_right _ _).trans (min_le_left _ _)
  have hrε : r ≤ ε / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hsub₀ : localDisk c r ⊆ localDisk c ρ₀ := fun _ hp ↦ lt_of_lt_of_le hp hr₀
  have hsubT : localDisk c r ⊆ localDisk c ρT := fun _ hp ↦ lt_of_lt_of_le hp hrT
  have hsubV : localDisk c r ⊆ V := fun p hp ↦
    (dist_le_localRadius c p).trans_lt (lt_of_lt_of_le hp hrε)
  have hsubU : localDisk c r ⊆ U := hsubV.trans (subset_closure.trans hVU)
  have hDr := hD₀.mono hsub₀
  have hwr : ∀ k ≤ 2, RadialJetLp k (4 - k) (localDisk c r) c D₀ :=
    fun k hk ↦ (hw₀ k hk).mono hsub₀
  have hGr : ∀ j, HasWeakPartialOn (localDisk c r) j (liftL2 ω) (G j) :=
    fun j ↦ (hG j).1.mono hsubU
  have hGwr : ∀ j, MemLp (fun p ↦ G j p / (localRadius c p : ℂ)) 2
      (volume.restrict (localDisk c r)) := by
    intro j
    apply memLp_div_localRadius hc
    exact ((hG j).2 V Metric.isOpen_ball hVc hVU).mono_measure
      (Measure.restrict_mono hsubV le_rfl)
  -- Identify the trace of the supplied remainder jet, rather than differentiating
  -- the continuous stream representative classically.
  have hQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (saddleQuadratic c a) := by
    exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ ↦ (p.2 - c.2) ^ 2 - (p.1 - c.1) ^ 2) by fun_prop))
  let Q := fun w ↦ classicalComplexJet w (saddleQuadratic c a)
  have hsum : HasWeakJetOn 2 (localDisk c r) (contStream ω)
      (fun w p ↦ D₀ w p + Q w p) := by
    convert hDr.add (classicalComplexJet_weak hQ 2 (localDisk c r)) using 1
    funext p
    simp only [sub_add_cancel]
  have hopen : IsOpen (localDisk c r) := by
    apply isOpen_lt _ continuous_const
    unfold localRadius
    fun_prop
  have heq := hsum.ae_eq hopen (streamJet2_weak ω (localDisk c r))
  have hpoisson : ∀ᵐ p, streamJet2 ω [0, 0] p + streamJet2 ω [1, 1] p = liftL2 ω p := by
    have he := ae_torusProj (Lp.coeFn_add
      (streamSecondPartial 0 0 ω) (streamSecondPartial 1 1 ω))
    rw [streamSecondPartial_add hω.1] at he
    filter_upwards [he] with p hp using hp.symm
  have hΔ : ∀ᵐ p ∂(volume.restrict (localDisk c r)),
      D₀ [0, 0] p + D₀ [1, 1] p = liftL2 ω p := by
    apply (ae_restrict_iff' hopen.measurableSet).mpr
    filter_upwards [heq [0, 0] (by decide), heq [1, 1] (by decide), hpoisson] with p hx hy hp hpr
    have hq := saddleQuadratic_harmonic c a p
    dsimp [Q] at hx hy
    linear_combination hx hpr + hy hpr - hq + hp
  obtain ⟨σ, hσ, hσr, E, hE, hE₀, hE3⟩ :=
    elliptic_weighted_third hr hDr hwr hGr hGwr hΔ
  have hσsub : localDisk c σ ⊆ localDisk c r := fun _ hp ↦ lt_of_lt_of_le hp hσr
  have hwE : ∀ k ≤ 3, RadialJetLp k (4 - k) (localDisk c σ) c E := by
    intro k hk
    by_cases hk2 : k ≤ 2
    · intro w hw
      rw [hE₀ w (by omega)]
      exact ((hwr k hk2).mono hσsub) w hw
    · have hk3 : k = 3 := by omega
      subst k
      exact hE3
  refine ⟨σ, hσ, a, E, (fun w p ↦ E w p + T w p), hE, ?_, hwE, ?_⟩
  · convert hE.add (hT.mono (hσsub.trans hsubT)) using 1
    funext p
    ring
  · intro k hk
    exact (hwE k hk).add ((hwT k hk).mono (hσsub.trans hsubT))

end NoEmbeddedEigenvalues
