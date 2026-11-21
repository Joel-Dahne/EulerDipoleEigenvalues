import NoEmbeddedEigenvalues.Transport.WeightedForcing.QuarterBulkTime
import NoEmbeddedEigenvalues.Transport.WeightedForcing.QuarterClockTrace
import NoEmbeddedEigenvalues.Transport.WeightedForcing.OrbitBulkFlux

/-!
# First-bulk endpoint energy from weak time differentiation

The normalized angular derivative is S times the actual fixed-time derivative.
Local weak data identify canonical section traces. The global trace bound uses
unit physical-time windows and the actual joint energy, without comparing
individual gradient traces in two different transverse charts.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

private def bulkClock (q : ℝ × ℝ) : ℝ × ℝ := (q.1, q.2 * orbitPeriod q.1)
private def bulkLevelCoefficient (i : Fin 2) (q : ℝ × ℝ) : ℂ :=
  (axisCoord i (deriv (fun h ↦ dipoleOrbit h (bulkClock q).2) q.1) : ℂ)
private def bulkAngularCoefficient (i : Fin 2) (q : ℝ × ℝ) : ℂ :=
  ((coordPartial 1 (fun p ↦ axisCoord i (actionAngleInv p)) q : ℝ) : ℂ)

private theorem bulkLevelCoefficient_smooth (i : Fin 2) :
    ContDiffOn ℝ ∞ (bulkLevelCoefficient i) actionStrip := by
  have hc : ContDiffOn ℝ ∞ bulkClock actionStrip :=
    contDiffOn_fst.prodMk (contDiffOn_snd.mul
      (contDiffOn_orbitPeriod.comp contDiffOn_fst (fun _ hq ↦ hq.1)))
  have hv : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦
      deriv (fun h ↦ dipoleOrbit h (bulkClock q).2) q.1) actionStrip := by
    intro q hq
    exact ((contDiffAt_orbit_level_derivative (t := (bulkClock q).2) hq.1).comp q
      (hc.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hq))).contDiffWithinAt
  fin_cases i
  · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiff_fst.comp_contDiffOn hv)
  · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiff_snd.comp_contDiffOn hv)

private theorem bulkAngularCoefficient_smooth (i : Fin 2) :
    ContDiffOn ℝ ∞ (bulkAngularCoefficient i) actionStrip := by
  have hP : ContDiffOn ℝ ∞ (fun q ↦ axisCoord i (actionAngleInv q)) actionStrip := by
    fin_cases i
    · exact contDiff_fst.comp_contDiffOn contDiffOn_actionAngleInv
    · exact contDiff_snd.comp_contDiffOn contDiffOn_actionAngleInv
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn
    (contDiffOn_coordPartial (isOpen_Ioo.prod isOpen_univ) hP 1)

private theorem bulkLevelCoefficient_time {q : ℝ × ℝ} (hq : q ∈ actionStrip) :
    coordPartial 1 (bulkLevelCoefficient 0) q = (orbitPeriod q.1 : ℂ) *
      ((Real.cos (dipoleOrbit q.1 (bulkClock q).2).2 *
        (deriv (fun h ↦ dipoleOrbit h (bulkClock q).2) q.1).2 : ℝ) : ℂ) ∧
    coordPartial 1 (bulkLevelCoefficient 1) q = (orbitPeriod q.1 : ℂ) *
      ((-Real.cos (dipoleOrbit q.1 (bulkClock q).2).1 *
        (deriv (fun h ↦ dipoleOrbit h (bulkClock q).2) q.1).1 : ℝ) : ℂ) := by
  have hd := (hasDerivAt_orbit_level_time (h := q.1) (t := (bulkClock q).2) hq.1).scomp q.2
    (hasDerivAt_mul_const (orbitPeriod q.1))
  have hx := ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.2 hd).ofReal_comp
  have hy := ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.2 hd).ofReal_comp
  constructor
  · simpa [bulkLevelCoefficient, bulkClock, axisCoord, coordPartial, partialY,
      smul_eq_mul, Complex.ofReal_mul] using hx.deriv
  · simpa [bulkLevelCoefficient, bulkClock, axisCoord, coordPartial, partialY,
      smul_eq_mul, Complex.ofReal_mul] using hy.deriv

private theorem bulkAngularCoefficient_time (q : ℝ × ℝ) :
    bulkAngularCoefficient 0 q = (orbitPeriod q.1 : ℂ) *
      (Real.sin (actionAngleInv q).2 : ℂ) ∧
    bulkAngularCoefficient 1 q = (orbitPeriod q.1 : ℂ) *
      (-Real.sin (actionAngleInv q).1 : ℂ) := by
  have hd := hasDerivAt_actionAngleInv_snd q.1 q.2
  have hx := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.2 hd
  have hy := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt q.2 hd
  constructor
  · simpa [bulkAngularCoefficient, axisCoord, coordPartial, partialY, dipoleVelocity,
      smul_eq_mul, Complex.ofReal_mul, Function.comp_def] using congrArg Complex.ofReal hx.deriv
  · simpa [bulkAngularCoefficient, axisCoord, coordPartial, partialY, dipoleVelocity,
      smul_eq_mul, Complex.ofReal_mul, Function.comp_def] using congrArg Complex.ofReal hy.deriv

/-- Local normalized weak time data for the specified first bulk. Every supplied
ordered Hessian entry keeps its index position. -/
theorem quarter_first_bulk_clock_data {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hcell : cellSquare ⊆ U)
    {J : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ i j, HasWeakPartialOn U i (J [j]) (J [i, j]))
    (hJL : ∀ j, MemLp (J [j]) 2 (volume.restrict U))
    (hJ₂L : ∀ i j, MemLp (J [i, j]) 2 (volume.restrict U))
    {a b h₀ : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < h₀) (hh₀ : h₀ < 1) :
    let R := Ioo a b ×ˢ Ioo (-1 / 4 : ℝ) (3 / 4)
    let F := fun q : ℝ × ℝ ↦
      quarterForcingLevelDerivative J (q.1, q.2 * orbitPeriod q.1)
    let H := fun q : ℝ × ℝ ↦ (orbitPeriod q.1 : ℂ) *
      quarterForcingLevelTimeDerivative J (q.1, q.2 * orbitPeriod q.1)
    HasWeakPartialOn R 1 F H ∧ MemLp F 2 (volume.restrict R) ∧
      MemLp H 2 (volume.restrict R) := by
  let K : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (-1 / 4 : ℝ) (3 / 4)
  let R : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo (-1 / 4 : ℝ) (3 / 4)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hRo : IsOpen R := isOpen_Ioo.prod isOpen_Ioo
  have hSo : IsOpen actionStrip := isOpen_Ioo.prod isOpen_univ
  have hRK : R ⊆ K := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hKs : K ⊆ actionStrip := fun q hq ↦
    ⟨⟨ha.trans_le hq.1.1, hq.1.2.trans_lt (hb.trans hh₀)⟩, mem_univ _⟩
  have hRs : R ⊆ actionStrip := hRK.trans hKs
  have hP (u : ℝ × ℝ → ℂ) (hu : MemLp u 2 (volume.restrict U)) :
      MemLp (u ∘ actionAngleInv) 2 (volume.restrict R) :=
    memLp_actionAngleInv_band hU hu ha hab hb hh₀ (fun p hp ↦ hcell hp.1.1)
  have hM (c F : ℝ × ℝ → ℂ) (hc : ContDiffOn ℝ ∞ c actionStrip)
      (hF : MemLp F 2 (volume.restrict R)) :
      MemLp (fun q ↦ c q * F q) 2 (volume.restrict R) :=
    memLp_mul_on_compact hK hRo.measurableSet hRK (hc.continuousOn.mono hKs) hF
  let P (j : Fin 2) := fun q ↦ bulkAngularCoefficient 0 q * J [0, j] (actionAngleInv q) +
    bulkAngularCoefficient 1 q * J [1, j] (actionAngleInv q)
  have hTw (j : Fin 2) : HasWeakPartialOn R 1 (J [j] ∘ actionAngleInv) (P j) :=
    (HasWeakPartialOn.comp_actionAngleInv_snd
      (fun i ↦ (hD i j).mono (sdiff_subset.trans hcell))).mono hRs
  have hPL (j : Fin 2) : MemLp (P j) 2 (volume.restrict R) :=
    (hM _ _ (bulkAngularCoefficient_smooth 0) (hP _ (hJ₂L 0 j))).add
      (hM _ _ (bulkAngularCoefficient_smooth 1) (hP _ (hJ₂L 1 j)))
  let E := fun q ↦
    (coordPartial 1 (bulkLevelCoefficient 0) q * J [0] (actionAngleInv q) +
      bulkLevelCoefficient 0 q * P 0 q) +
    (coordPartial 1 (bulkLevelCoefficient 1) q * J [1] (actionAngleInv q) +
      bulkLevelCoefficient 1 q * P 1 q)
  have hw := ((hTw 0).mul_contDiffOn hRo ((bulkLevelCoefficient_smooth 0).mono hRs)).add
    ((hTw 1).mul_contDiffOn hRo ((bulkLevelCoefficient_smooth 1).mono hRs))
  have hFL : MemLp (fun q ↦ quarterForcingLevelDerivative J (bulkClock q)) 2
      (volume.restrict R) :=
    (hM _ _ (bulkLevelCoefficient_smooth 0) (hP _ (hJL 0))).add
      (hM _ _ (bulkLevelCoefficient_smooth 1) (hP _ (hJL 1)))
  have hEL : MemLp E 2 (volume.restrict R) :=
    ((hM _ _ (contDiffOn_coordPartial hSo (bulkLevelCoefficient_smooth 0) 1)
      (hP _ (hJL 0))).add (hM _ _ (bulkLevelCoefficient_smooth 0) (hPL 0))).add
    ((hM _ _ (contDiffOn_coordPartial hSo (bulkLevelCoefficient_smooth 1) 1)
      (hP _ (hJL 1))).add (hM _ _ (bulkLevelCoefficient_smooth 1) (hPL 1)))
  have he (q : ℝ × ℝ) (hq : q ∈ R) : E q =
      (orbitPeriod q.1 : ℂ) * quarterForcingLevelTimeDerivative J (bulkClock q) := by
    dsimp only [E]
    rw [(bulkLevelCoefficient_time (hRs hq)).1, (bulkLevelCoefficient_time (hRs hq)).2]
    dsimp only [P]
    rw [(bulkAngularCoefficient_time q).1, (bulkAngularCoefficient_time q).2]
    simp only [quarterForcingLevelTimeDerivative, Fin.sum_univ_two, bulkLevelCoefficient,
      bulkClock, axisCoord, actionAngleInv, dipoleVelocity, ↓reduceIte,
      show (1 : Fin 2) ≠ 0 by decide]
    push_cast
    ring
  refine ⟨?_, hFL, hEL.ae_eq ?_⟩
  · exact hw.congr_ae_on hRo.measurableSet (Eventually.of_forall fun _ _ ↦ rfl)
      (Eventually.of_forall fun q hq ↦ he q hq)
  · filter_upwards [ae_restrict_mem hRo.measurableSet] with q hq
    exact he q hq

/-- A nonvanishing smooth multiplier preserves the existence of a continuous
section germ, including the exceptional fallback case of the canonical trace. -/
private theorem interior_trace_mul_nonzero {f g : ℝ → ℂ}
    (hg : Continuous g) (hg0 : g 0 ≠ 0) :
    interiorSectionTrace (fun s ↦ g s * f s) = g 0 * interiorSectionTrace f := by
  classical
  by_cases hf : HasContinuousSectionGerm f
  · exact interiorSectionTrace_mul_continuous hf hg
  have hgf : ¬ HasContinuousSectionGerm (fun s ↦ g s * f s) := by
    rintro ⟨W, a, b, ha, hb, hW, hWe⟩
    have hne : ∀ᶠ s in 𝓝 (0 : ℝ), g s ≠ 0 := hg.continuousAt.eventually_ne hg0
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 hne
    let c := max a (-δ)
    let d := min b δ
    have hc : c < 0 := max_lt ha (by linarith)
    have hd : 0 < d := lt_min hb hδ
    have hsub : Ioo c d ⊆ Ioo a b := Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)
    have hno (s : ℝ) (hs : s ∈ Ioo c d) : g s ≠ 0 := by
      apply hδsub
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨(le_max_right a (-δ)).trans_lt hs.1,
        hs.2.trans_le (min_le_right b δ)⟩
    apply hf
    refine ⟨fun s ↦ W s / g s, c, d, hc, hd,
      (hW.mono hsub).div hg.continuousOn hno, ?_⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hWe,
      ae_restrict_mem measurableSet_Ioo] with s he hs
    rw [he]
    exact mul_div_cancel_left₀ (f s) (hno s hs)
  simp only [interiorSectionTrace, dite_eq_right hf, dite_eq_right hgf, mul_zero]

/-- The complete first-bulk boundary potentials have genuine L2 level norms on
one collar for every real frequency. Individual gradient traces are not compared
between the normalized-angle and affine-ray charts. -/
theorem quarter_first_bulk_endpoint_energy {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hcell : cellSquare ⊆ U)
    {J : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ i j, HasWeakPartialOn U i (J [j]) (J [i, j]))
    (hJL : ∀ w, w.length ≤ 2 → MemLp (J w) 2 (volume.restrict U))
    (hDw : ∀ j : Fin 2, MemLp (fun p ↦ J [j] p /
      (Real.rpow (saddleDist p) (3 / 2) : ℂ)) 2 (volume.restrict cellSquare)) :
    ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧ ∀ μ : ℝ, ∀ side : Bool,
      MemLp (quarterFirstBulkTrace μ J ((if side then 1 else -1 : ℝ) / 8)) 2
        (volume.restrict (Ioo 0 b)) := by
  have htop := tendsto_orbitPeriod_atTop.eventually (eventually_ge_atTop (4 : ℝ))
  obtain ⟨r, hr, hSr⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 htop
  let c := min r (1 / 2)
  have hc : 0 < c := lt_min hr (by norm_num)
  have hc1 : c < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hJLcell (w) (hw : w.length ≤ 2) :=
    (hJL w hw).mono_measure (Measure.restrict_mono_set _ hcell)
  obtain ⟨b, hb, hbc, hG, hH⟩ := quarter_first_bulk_time_energy hc hc1 hJLcell hDw
  have hbh : b < 1 / 2 := hbc.trans_le (min_le_right _ _)
  have hb1 : b < 1 := by linarith
  have hSb (h : ℝ) (hh : h ∈ Ioo 0 b) : 4 ≤ orbitPeriod h :=
    hSr ⟨hh.1, (hh.2.trans hbc).trans_le (min_le_left _ _)⟩
  have hloc (a d : ℝ) (ha : 0 < a) (had : a < d) (hd : d < b) :=
    quarter_first_bulk_clock_data hU hcell hD (fun j ↦ hJL [j] (by simp))
      (fun i j ↦ hJL [i, j] (by simp)) ha had hd hb1
  have hTr (side : Bool) := memLp_quarter_clock_trace hG hH hSb hloc side
  refine ⟨b, hb, hbh, ?_⟩
  intro μ side
  let θ : ℝ := (if side then 1 else -1) / 8
  let φ : ℝ → ℂ := fun h ↦ (θ : ℂ) *
    Complex.exp (-Complex.I * ((μ * (θ * orbitPeriod h) : ℝ) : ℂ))
  have hSc : ContinuousOn orbitPeriod (Ioo 0 b) :=
    contDiffOn_orbitPeriod.continuousOn.mono (Ioo_subset_Ioo le_rfl hb1.le)
  have hφ : ContinuousOn φ (Ioo 0 b) := continuousOn_const.mul
    (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_const.mul (continuousOn_const.mul hSc)))))
  have hφbound (h : ℝ) : ‖φ h‖ ≤ 1 := by
    dsimp [φ]
    rw [norm_mul, Complex.norm_exp]
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_self, neg_zero, Real.exp_zero,
      mul_one, Complex.norm_real, Real.norm_eq_abs]
    cases side <;> norm_num [θ]
  have hm := (hTr side).of_le_mul (c := 1)
    ((hφ.aestronglyMeasurable measurableSet_Ioo).mul (hTr side).aestronglyMeasurable)
    (Eventually.of_forall fun h ↦ by
      rw [Pi.mul_apply, norm_mul]
      exact (mul_le_mul_of_nonneg_right (hφbound h) (norm_nonneg _)))
  apply hm.ae_eq
  exact Eventually.of_forall fun h ↦ by
    dsimp only [Pi.mul_apply, φ]
    rw [quarterFirstBulkTrace, interior_trace_mul_nonzero]
    · simp only [add_zero, θ]
    · fun_prop
    · simp only [add_zero, mul_ne_zero_iff, Complex.ofReal_ne_zero]
      cases side <;> norm_num [θ]

end NoEmbeddedEigenvalues
