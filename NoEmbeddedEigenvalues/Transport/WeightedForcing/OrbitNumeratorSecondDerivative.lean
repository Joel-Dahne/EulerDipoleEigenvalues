module

public import NoEmbeddedEigenvalues.Transport.WeightedForcing.OrbitBulkFlux
public import NoEmbeddedEigenvalues.Transport.WeightedGains.OrbitNumeratorH2
public import NoEmbeddedEigenvalues.Analysis.Inequalities.IntervalH1Multipliers
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.LocalContinuousRepresentative

/-!
# The second weak moving-endpoint numerator formula

Blueprint: `def:numerator-endpoint-flux`, `def:numerator-second-derivative`,
`lem:numerator-endpoint-flux-derivative`, `lem:numerator-second-moving-endpoints`.

Differentiate the rough first fixed-time bulk by a canonical transverse flux.
Differentiate the actual continuous endpoint values separately. The original
numerator and its ordinary first derivative are retained, as are all ordered
entries of the supplied forcing jet. The result is local H² with the explicit
second candidate; it does not assert its global h-weighted L² norm.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- Smooth scalar coefficient of one moving endpoint value. -/
def quarterEndpointCoefficient (lam ε h : ℝ) : ℂ :=
  ((deriv eighthPeriod h : ℝ) : ℂ) *
    Complex.exp (-Complex.I * ((lam * (ε * eighthPeriod h) : ℝ) : ℂ))

/-- The continuous endpoint contribution in the original first formula. -/
def quarterNumeratorEndpointFlux (lam : ℝ) (g : ℝ × ℝ → ℂ) (h : ℝ) : ℂ :=
  quarterEndpointCoefficient lam 1 h * g (dipoleOrbit h (1 * eighthPeriod h)) +
    quarterEndpointCoefficient lam (-1) h * g (dipoleOrbit h (-1 * eighthPeriod h))

/-- Derivative of the endpoint contribution, using canonical normalized traces
of the original supplied first entries rather than raw gradient values on rays. -/
def quarterNumeratorEndpointDerivative (lam : ℝ) (g : ℝ × ℝ → ℂ)
    (D : List (Fin 2) → ℝ × ℝ → ℂ) (h : ℝ) : ℂ :=
  (deriv (quarterEndpointCoefficient lam 1) h * g (dipoleOrbit h (1 * eighthPeriod h)) +
    quarterEndpointCoefficient lam 1 h * interiorSectionTrace
      (fun s ↦ actionAnglePullbackGradient (fun j ↦ D [j]) 0 (h, 1 / 8 + s))) +
  (deriv (quarterEndpointCoefficient lam (-1)) h * g (dipoleOrbit h (-1 * eighthPeriod h)) +
    quarterEndpointCoefficient lam (-1) h * interiorSectionTrace
      (fun s ↦ actionAnglePullbackGradient (fun j ↦ D [j]) 0 (h, -1 / 8 + s)))

/-- The second fixed-time bulk and both kinds of canonical endpoint terms. -/
def quarterNumeratorSecondDerivative (lam : ℝ) (g : ℝ × ℝ → ℂ)
    (D : List (Fin 2) → ℝ × ℝ → ℂ) (h : ℝ) : ℂ :=
  (quarterSecondBulk lam D h + ((deriv orbitPeriod h : ℝ) : ℂ) *
    (quarterFirstBulkTrace lam D (1 / 8) h - quarterFirstBulkTrace lam D (-1 / 8) h)) +
      quarterNumeratorEndpointDerivative lam g D h

/-- The old supplied-gradient candidate splits into its actual fixed-time bulk
and the continuous endpoint term, with no change to either representative. -/
theorem quarterNumeratorDerivative_eq_bulk_add_endpoints (lam : ℝ) (g : ℝ × ℝ → ℂ)
    (D : List (Fin 2) → ℝ × ℝ → ℂ) (h : ℝ) :
    quarterNumeratorDerivative lam g D h =
      (∫ t in (-eighthPeriod h)..eighthPeriod h,
        quarterForcingLevelDerivative D (h, t) *
          Complex.exp (-Complex.I * ((lam * t : ℝ) : ℂ))) +
        quarterNumeratorEndpointFlux lam g h := by
  simp only [quarterNumeratorDerivative, quarterNumeratorEndpointFlux, quarterEndpointCoefficient,
    one_mul, neg_mul, mul_neg, Complex.ofReal_neg, neg_neg]
  ring

/-- Endpoint coefficients are smooth at every positive noncentral level. -/
theorem contDiffOn_quarterEndpointCoefficient (lam ε : ℝ) :
    ContDiffOn ℝ ∞ (quarterEndpointCoefficient lam ε) (Ioo 0 1) := by
  have hL := contDiffOn_eighthPeriod
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (hL.deriv_of_isOpen isOpen_Ioo (by simp))).mul
      ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
        (contDiffOn_const.mul (contDiffOn_const.mul hL)))).cexp)

/-- The actual endpoint term has the explicit canonical derivative on each
compact collar interval, without a continuous-gradient premise. -/
theorem IsTransportPair.quarterNumeratorEndpointFlux_hasIntervalH1
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : ∀ j, HasWeakPartialOn U j f (D [j]))
    {a b h₀ : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < h₀) (hh₀ : h₀ < 1) (μ : ℝ) :
    HasIntervalH1 a b (quarterNumeratorEndpointFlux μ g)
      (quarterNumeratorEndpointDerivative μ g D) := by
  have hs : Icc a b ⊆ Ioo (0 : ℝ) 1 := fun h hh ↦
    ⟨ha.trans_le hh.1, hh.2.trans_lt (hb.trans hh₀)⟩
  have hE (ε : ℝ) (hε : ε = -1 ∨ ε = 1) :=
    ((hp.quarterEndpoint_forcing_h1Loc hcell hg hfg hD hh₀ hε) a b ha hab hb).mul_contDiffOn_open
      isOpen_Ioo (contDiffOn_quarterEndpointCoefficient μ ε) hs
  exact (hE 1 (Or.inr rfl)).add (hE (-1) (Or.inl rfl))

/-- Actual second moving-endpoint weak differentiation, retaining the original
continuous numerator, its ordinary first derivative, and every supplied ordered
jet entry. Its second candidate consists of the genuine fixed-time second bulk
and canonical endpoint terms; no global weighted second norm is assumed. -/
theorem IsTransportPair.quarterNumerator_hasIntervalH2_derivative
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : List (Fin 2) → ℝ × ℝ → ℂ} (hJ : HasWeakJetOn 2 U f D)
    {a b h₀ : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < h₀) (hh₀ : h₀ < 1) (μ : ℝ) :
    HasIntervalH2 a b (quarterNumerator μ g) (deriv (quarterNumerator μ g))
      (quarterNumeratorSecondDerivative μ g D) := by
  have hU := hp.isOrbitUnion.1
  have hD (j : Fin 2) : HasWeakPartialOn U j f (D [j]) := by
    simpa only [hJ.1] using hJ.2 [] (by simp) j
  have hDL := hp.memSobolevOn.memLp_weakJet hU hJ
  have he := (ae_restrict_iff' hU.measurableSet).1 hfg
  have hDg (j : Fin 2) : HasWeakPartialOn U j g (D [j]) :=
    (hD j).congr_ae_on hU.measurableSet he (Eventually.of_forall fun _ _ ↦ rfl)
  have hfirst := quarterNumerator_hasIntervalH1_derivative hU hg
    (hp.memSobolevOn.1.ae_eq hfg) hDg (fun j ↦ hDL [j] (by simp))
    (subset_closure.trans hcell) ha hab hb hh₀ (lam := μ)
  have hA : orbitAnnulus 0 h₀ ⊆ U := fun p hp ↦ hcell (subset_closure hp.1.1)
  have hN := hp.quarterNumerator_h2Loc hg hfg hh₀ hA μ a b ha hab hb
  have hE := hp.quarterNumeratorEndpointFlux_hasIntervalH1 hcell hg hfg hD ha hab hb hh₀ μ
  let A : ℝ → ℂ := fun h ↦ deriv (quarterNumerator μ g) h - quarterNumeratorEndpointFlux μ g h
  have hAc : ContinuousOn A (Ioo a b) :=
    (hN.2.continuousOn_Ioo hab).sub (hE.continuousOn_Ioo hab)
  have hAe : A =ᵐ[volume.restrict (Ioo a b)]
      (fun h ↦ ∫ t in (-eighthPeriod h)..eighthPeriod h,
        quarterForcingLevelDerivative D (h, t) *
          Complex.exp (-Complex.I * ((μ * t : ℝ) : ℂ))) := by
    filter_upwards [ae_restrict_of_ae hfirst.hasDerivAt_ae,
      ae_restrict_mem measurableSet_Ioo] with h hh hhI
    dsimp only [A]
    rw [(hh hhI).deriv, quarterNumeratorDerivative_eq_bulk_add_endpoints]
    ring
  have hB := quarterFirstBulk_hasIntervalH1_of_ae_eq hU (subset_closure.trans hcell)
    (fun i j ↦ hJ.2 [j] (by simp) i) (fun j ↦ hDL [j] (by simp))
    (fun i j ↦ hDL [i, j] (by simp)) ha hab hb hh₀ hAc hAe
  refine ⟨hN.1, (hB.add hE).congr_Ioo ?_⟩
  intro h _
  exact sub_add_cancel _ _

/-- The same formula accepts a jet of the continuous representative, as in the
stronger weighted numerator interface. Only the temporary nil entry is changed;
every first/second function in the returned candidate is the supplied one. -/
theorem IsTransportPair.quarterNumerator_hasIntervalH2_derivative_of_rep_jet
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : List (Fin 2) → ℝ × ℝ → ℂ} (hJ : HasWeakJetOn 2 U g D)
    {a b h₀ : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < h₀) (hh₀ : h₀ < 1) (μ : ℝ) :
    HasIntervalH2 a b (quarterNumerator μ g) (deriv (quarterNumerator μ g))
      (quarterNumeratorSecondDerivative μ g D) := by
  let J : List (Fin 2) → ℝ × ℝ → ℂ := fun w ↦ if w = [] then f else D w
  have hU := hp.isOrbitUnion.1
  have he := (ae_restrict_iff' hU.measurableSet).1 hfg
  have hJf : HasWeakJetOn 2 U f J := by
    refine ⟨by simp only [J, ↓reduceIte], ?_⟩
    intro w hw j
    cases w with
    | nil =>
      have hd : HasWeakPartialOn U j g (D [j]) := by
        simpa only [hJ.1] using hJ.2 [] hw j
      simpa only [J, List.cons_ne_nil, ↓reduceIte] using
        hd.congr_ae_on hU.measurableSet (he.mono fun _ hp hpU ↦ (hp hpU).symm)
          (Eventually.of_forall fun _ _ ↦ rfl)
    | cons i w =>
      simpa only [J, List.cons_ne_nil, ↓reduceIte] using hJ.2 (i :: w) hw j
  have hN := hp.quarterNumerator_hasIntervalH2_derivative hcell hg hfg hJf ha hab hb hh₀ μ
  change HasIntervalH2 a b (quarterNumerator μ g) (deriv (quarterNumerator μ g))
    (fun h ↦ quarterNumeratorSecondDerivative μ g J h) at hN
  change HasIntervalH2 a b (quarterNumerator μ g) (deriv (quarterNumerator μ g))
    (fun h ↦ quarterNumeratorSecondDerivative μ g D h)
  simpa only [quarterNumeratorSecondDerivative, quarterSecondBulk,
    quarterForcingSecondLevelDerivative, quarterFirstBulkTrace, quarterForcingLevelDerivative,
    quarterNumeratorEndpointDerivative, actionAnglePullbackGradient,
    List.ofFn_succ, J, List.cons_ne_nil, ↓reduceIte] using hN

/-- One compatible local H² pair on any collar below level one, with the
canonical second moving-endpoint candidate rather than a replacement jet. -/
theorem IsTransportPair.quarterNumerator_second_derivative_h2Loc
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : List (Fin 2) → ℝ × ℝ → ℂ} (hJ : HasWeakJetOn 2 U f D)
    {h₀ : ℝ} (hh₀ : h₀ < 1) (μ : ℝ) :
    HasIntervalH2Loc 0 h₀ (quarterNumerator μ g) (deriv (quarterNumerator μ g))
      (quarterNumeratorSecondDerivative μ g D) := by
  intro a b ha hab hb
  exact hp.quarterNumerator_hasIntervalH2_derivative hcell hg hfg hJ ha hab hb hh₀ μ

/-- On every compact collar interval, the canonical second candidate agrees
with the ordinary second scalar derivative almost everywhere. -/
theorem IsTransportPair.quarterNumerator_second_derivative_ae
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : List (Fin 2) → ℝ × ℝ → ℂ} (hJ : HasWeakJetOn 2 U f D)
    {a b h₀ : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < h₀) (hh₀ : h₀ < 1) (μ : ℝ) :
    deriv (deriv (quarterNumerator μ g)) =ᵐ[volume.restrict (Ioo a b)]
      quarterNumeratorSecondDerivative μ g D := by
  have hN := hp.quarterNumerator_hasIntervalH2_derivative hcell hg hfg hJ ha hab hb hh₀ μ
  filter_upwards [ae_restrict_of_ae hN.2.hasDerivAt_ae, ae_restrict_mem measurableSet_Ioo]
    with h hh hhI
  exact (hh hhI).deriv

/-- The standing H² forcing constructs all second entries while retaining the
original first gradient exactly. The continuous representative and any existing
numerator collar can be reused; one jet works for every real frequency. -/
theorem IsTransportPair.exists_quarterNumerator_second_derivative_with_rep
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    (hg : ContinuousOn g U) (hfg : f =ᵐ[volume.restrict U] g)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j)) :
    ∃ J : List (Fin 2) → ℝ × ℝ → ℂ, HasWeakJetOn 2 U f J ∧
      (∀ j, J [j] = D j) ∧ ∀ h₀ : ℝ, h₀ < 1 → ∀ μ : ℝ,
        HasIntervalH2Loc 0 h₀ (quarterNumerator μ g) (deriv (quarterNumerator μ g))
          (quarterNumeratorSecondDerivative μ g J) := by
  obtain ⟨J, hJ, hJD⟩ := hp.memSobolevOn.exists_weakJet_two_with_first hp.isOrbitUnion.1 hD
  exact ⟨J, hJ, hJD, fun _ hh₀ μ ↦
    hp.quarterNumerator_second_derivative_h2Loc hcell hg hfg hJ hh₀ μ⟩

/-- Original pair and supplied-gradient inputs alone produce both the continuous
forcing representative and the genuine local second moving-endpoint formula.
No Hessian, continuous gradient, or scalar regularity is an extra hypothesis. -/
theorem IsTransportPair.exists_quarterNumerator_second_derivative
    {lam : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hcell : closure cellSquare ⊆ U)
    {D : Fin 2 → ℝ × ℝ → ℂ} (hD : ∀ j, HasWeakPartialOn U j f (D j)) :
    ∃ (g : ℝ × ℝ → ℂ) (J : List (Fin 2) → ℝ × ℝ → ℂ),
      ContinuousOn g U ∧ f =ᵐ[volume.restrict U] g ∧ HasWeakJetOn 2 U f J ∧
        (∀ j, J [j] = D j) ∧ ∀ h₀ : ℝ, h₀ < 1 → ∀ μ : ℝ,
          HasIntervalH2Loc 0 h₀ (quarterNumerator μ g) (deriv (quarterNumerator μ g))
            (quarterNumeratorSecondDerivative μ g J) := by
  obtain ⟨g, hg, hfg⟩ := exists_continuousOn_rep_of_memSobolevLocOn_two
    hp.isOrbitUnion.1 hp.memSobolevOn.memSobolevLocOn
  obtain ⟨J, hJ, hJD, hN⟩ := hp.exists_quarterNumerator_second_derivative_with_rep hcell hg hfg hD
  exact ⟨g, J, hg, hfg, hJ, hJD, hN⟩

end NoEmbeddedEigenvalues
