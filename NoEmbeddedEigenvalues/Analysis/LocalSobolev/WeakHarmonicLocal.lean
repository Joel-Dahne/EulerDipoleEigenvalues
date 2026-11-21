module

public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.PlaneConvolution
public import NoEmbeddedEigenvalues.Analysis.LocalSobolev.RadialMeanValue
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Smooth representatives of compact-test harmonic data

Shrinking generic bumps are used only as an approximate identity. The fixed
kernel used for harmonic mean value is explicitly Euclidean radial. Finite
Fubini integrals exchange the kernels. Lebesgue differentiation then identifies
the raw datum with a fixed smooth convolution, jointly a.e. on an open patch.
Continuous uniqueness glues these representatives on the entire original open
set; the final a.e. identity uses a countable subcover.
-/

@[expose] public section

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Metric Filter InnerProductSpace ContinuousLinearMap
open scoped ContDiff Convolution Topology

local instance : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- A bounded-shape shrinking approximate identity for the actual product metric. -/
def planeApproxBump (n : ℕ) : ContDiffBump (0 : ℝ × ℝ) :=
  ⟨(1 / ((n : ℝ) + 1)) / 2, 1 / ((n : ℝ) + 1), by positivity,
    half_lt_self (by positivity)⟩

/-- Complex-valued actual normalized kernels. -/
def planeApproxKernel (n : ℕ) (p : ℝ × ℝ) : ℂ :=
  (planeApproxBump n).normed volume p

private theorem approx_radius_tendsto :
    Tendsto (fun n ↦ (planeApproxBump n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

private theorem contDiff_planeApproxKernel (n : ℕ) :
    ContDiff ℝ ∞ (planeApproxKernel n) :=
  Complex.ofRealCLM.contDiff.comp (planeApproxBump n).contDiff_normed

private theorem compact_planeApproxKernel (n : ℕ) : HasCompactSupport (planeApproxKernel n) := by
  change HasCompactSupport (Complex.ofReal ∘ (planeApproxBump n).normed volume)
  exact (planeApproxBump n).hasCompactSupport_normed.comp_left (g := Complex.ofReal)
    Complex.ofReal_zero

private theorem support_planeApproxKernel (n : ℕ) :
    tsupport (planeApproxKernel n) ⊆ closedBall 0 (planeApproxBump n).rOut := by
  exact (tsupport_comp_subset Complex.ofReal_zero ((planeApproxBump n).normed volume)).trans_eq
    (planeApproxBump n).tsupport_normed_eq

private theorem approx_convolution_eq (n : ℕ) (f : ℝ × ℝ → ℂ) :
    planeConvolution f (planeApproxKernel n) =
      (planeApproxBump n).normed volume ⋆[lsmul ℝ ℝ] f := by
  rw [planeConvolution_comm]
  exact planeConvolution_ofReal _ f

/-- The actual smooth approximants converge to the original raw datum a.e. -/
theorem planeApproxConvolution_tendsto_ae {f : ℝ × ℝ → ℂ} (hf : LocallyIntegrable f) :
    ∀ᵐ x, Tendsto (fun n ↦ planeConvolution f (planeApproxKernel n) x) atTop (𝓝 (f x)) := by
  have hshape : ∀ᶠ n in atTop, (planeApproxBump n).rOut ≤ 2 * (planeApproxBump n).rIn :=
    Eventually.of_forall fun n ↦ by dsimp [planeApproxBump]; linarith
  simpa only [approx_convolution_eq] using
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable approx_radius_tendsto hshape hf

/-- Smooth fixed convolutions have pointwise approximate-identity convergence. -/
theorem planeApproxConvolution_tendsto_continuous {f : ℝ × ℝ → ℂ} (hf : Continuous f)
    (x : ℝ × ℝ) :
    Tendsto (fun n ↦ planeConvolution f (planeApproxKernel n) x) atTop (𝓝 (f x)) := by
  simpa only [approx_convolution_eq] using
    ContDiffBump.convolution_tendsto_right_of_continuous approx_radius_tendsto hf x

/-- Joint restricted a.e. equality transports a compact test pairing; there is
no restriction of raw representatives to a curve. -/
theorem integral_mul_test_congr_ae {U : Set (ℝ × ℝ)} (hU : MeasurableSet U)
    {f g φ : ℝ × ℝ → ℂ} (hfg : f =ᵐ[volume.restrict U] g) (hφ : tsupport φ ⊆ U) :
    (∫ p, f p * φ p) = ∫ p, g p * φ p := by
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hU).mp hfg] with p hp
  by_cases hpU : p ∈ U
  · rw [hp hpU]
  · have hz : φ p = 0 := image_eq_zero_of_notMem_tsupport (fun hm ↦ hpU (hφ hm))
    simp only [hz, mul_zero]

/-- One fixed smooth radial convolution represents the raw weak-harmonic datum
on a whole open patch. The fourfold surrounding ball stays inside the original
weak domain, so no weak identity is asserted across the extension boundary. -/
theorem weak_harmonic_local_smoothing {U : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℂ}
    (hf : Integrable f)
    (hw : ∀ φ, IsTestFunctionOn U φ → ∫ p, f p * planeLaplacian φ p = 0)
    {c : ℝ × ℝ} {r : ℝ} (hr : 0 < r) (hball : closedBall c (4 * r) ⊆ U) :
    let g := planeConvolution f (radialPlaneKernel r)
    ContDiff ℝ ∞ g ∧ g =ᵐ[volume.restrict (ball c r)] f ∧
      ∀ p ∈ ball c r, planeLaplacian g p = 0 := by
  let K := radialPlaneKernel r
  let g := planeConvolution f K
  let M (n : ℕ) := planeConvolution f (planeApproxKernel n)
  have hK := contDiff_radialPlaneKernel r
  have hKc := hasCompactSupport_radialPlaneKernel hr
  have hg : ContDiff ℝ ∞ g := contDiff_planeConvolution hf.locallyIntegrable hK hKc
  have hM (n : ℕ) : ContDiff ℝ ∞ (M n) :=
    contDiff_planeConvolution hf.locallyIntegrable (contDiff_planeApproxKernel n)
      (compact_planeApproxKernel n)
  have hsmall : ∀ᶠ n in atTop, (planeApproxBump n).rOut ≤ r :=
    (approx_radius_tendsto.eventually (gt_mem_nhds hr)).mono fun _ hn ↦ hn.le
  have hΔM (n : ℕ) (hn : (planeApproxBump n).rOut ≤ r) :
      ∀ p ∈ ball c (3 * r), planeLaplacian (M n) p = 0 := by
    intro p hp
    apply planeLaplacian_smoothing_eq_zero hf.locallyIntegrable hw
      (contDiff_planeApproxKernel n) (compact_planeApproxKernel n) p
    intro q hq
    apply hball
    have hqn : ‖q‖ ≤ (planeApproxBump n).rOut := by
      simpa only [mem_closedBall, dist_zero_right] using support_planeApproxKernel n hq
    have hpn : ‖p - c‖ < 3 * r := by simpa only [mem_ball, dist_eq_norm] using hp
    change dist (p - q) c ≤ 4 * r
    rw [dist_eq_norm, show p - q - c = (p - c) - q by abel]
    exact (norm_sub_le _ _).trans (by linarith)
  have hmean (n : ℕ) (hn : (planeApproxBump n).rOut ≤ r) (x : ℝ × ℝ)
      (hx : x ∈ ball c r) : planeConvolution K (M n) x = M n x := by
    have hHC := harmonicOnNhd_complex_of_plane isOpen_ball (hM n) (hΔM n hn)
    have hcover : closedBall (Complex.equivRealProdCLM.symm x) r ⊆
        Complex.equivRealProdCLM ⁻¹' ball c (3 * r) := by
      intro z hz
      have hdist : dist (Complex.equivRealProdCLM z) x ≤ r := by
        calc
          _ = ‖Complex.equivRealProdCLM (z - Complex.equivRealProdCLM.symm x)‖ := by
            rw [map_sub, ContinuousLinearEquiv.apply_symm_apply, dist_eq_norm]
          _ ≤ ‖z - Complex.equivRealProdCLM.symm x‖ := Complex.equivRealProd_apply_le _
          _ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hz
      change dist (Complex.equivRealProdCLM z) c < 3 * r
      have hx' : dist x c < r := hx
      exact (dist_triangle _ x _).trans_lt (by linarith)
    simpa only [planeConvolution, convolution_def, mul_apply'] using
      integral_radialPlaneKernel_mul_harmonic hr (hM n).continuous x (hHC.mono hcover)
  have hex (n : ℕ) (x : ℝ × ℝ) :
      planeConvolution K (M n) x = planeConvolution g (planeApproxKernel n) x := by
    change planeConvolution K (planeConvolution f (planeApproxKernel n)) x = _
    rw [planeConvolution_comm f (planeApproxKernel n),
      planeConvolution_swap_kernels hK.continuous hKc
        (contDiff_planeApproxKernel n).continuous (compact_planeApproxKernel n) hf,
      planeConvolution_comm K f, planeConvolution_comm (planeApproxKernel n)]
  have hae : g =ᵐ[volume.restrict (ball c r)] f := by
    filter_upwards [ae_restrict_of_ae (planeApproxConvolution_tendsto_ae hf.locallyIntegrable),
      ae_restrict_mem isOpen_ball.measurableSet] with x hlim hx
    have hevent : (fun n ↦ M n x) =ᶠ[atTop]
        (fun n ↦ planeConvolution g (planeApproxKernel n) x) := by
      filter_upwards [hsmall] with n hn
      rw [← hmean n hn x hx, hex]
    exact tendsto_nhds_unique
      ((planeApproxConvolution_tendsto_continuous hg.continuous x).congr' hevent.symm) hlim
  refine ⟨hg, hae, ?_⟩
  apply planeLaplacian_eq_zero_of_test isOpen_ball hg
  intro φ hφ
  rw [integral_mul_test_congr_ae isOpen_ball.measurableSet hae hφ.planeLaplacian.tsupport_subset]
  apply hw φ (hφ.mono ?_)
  intro p hp
  apply hball
  exact closedBall_subset_closedBall (show r ≤ 4 * r by linarith) (ball_subset_closedBall hp)

private theorem coordPartial_germ_eq {a b : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (he : a =ᶠ[𝓝 p] b) (j : Fin 2) : coordPartial j a p = coordPartial j b p := by
  have hx := he.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto p.1)
  have hy := he.comp_tendsto ((continuous_const.prodMk continuous_id).tendsto p.2)
  simp only [Function.comp_def, id_eq] at hx hy
  unfold coordPartial partialX partialY
  split_ifs
  · exact hx.deriv_eq
  · exact hy.deriv_eq

private theorem planeLaplacian_germ_eq {a b : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (he : a =ᶠ[𝓝 p] b) : planeLaplacian a p = planeLaplacian b p := by
  have hfirst (j : Fin 2) : coordPartial j a =ᶠ[𝓝 p] coordPartial j b :=
    (eventually_eventually_nhds.mpr he).mono fun _ hq ↦ coordPartial_germ_eq hq j
  exact congrArg₂ (· + ·) (coordPartial_germ_eq (hfirst 0) 0)
    (coordPartial_germ_eq (hfirst 1) 1)

/-- A weak-harmonic integrable datum has a smooth harmonic representative on
its entire original open domain. Local smooth representatives agree pointwise
on overlaps; a countable subcover is used only for the final joint a.e. identity. -/
theorem weak_harmonic_smooth_rep {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {f : ℝ × ℝ → ℂ} (hf : Integrable f)
    (hw : ∀ φ, IsTestFunctionOn U φ → ∫ p, f p * planeLaplacian φ p = 0) :
    ∃ h : ℝ × ℝ → ℂ, ContDiffOn ℝ ∞ h U ∧
      (∀ p ∈ U, planeLaplacian h p = 0) ∧ h =ᵐ[volume.restrict U] f := by
  classical
  have hloc (p : ℝ × ℝ) (hp : p ∈ U) :
      ∃ W : Set (ℝ × ℝ), IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧
        ∃ g : ℝ × ℝ → ℂ, ContDiff ℝ ∞ g ∧
          g =ᵐ[volume.restrict W] f ∧ ∀ q ∈ W, planeLaplacian g q = 0 := by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU p hp
    let r := ε / 8
    have hr : 0 < r := by dsimp [r]; positivity
    have hball : closedBall p (4 * r) ⊆ U := by
      intro q hq
      apply hεU
      change dist q p < ε
      have hq' : dist q p ≤ 4 * r := hq
      dsimp [r] at hq'
      linarith
    obtain ⟨hg, hae, hΔ⟩ := weak_harmonic_local_smoothing hf hw hr hball
    refine ⟨ball p r, isOpen_ball, mem_ball_self hr, ?_, _, hg, hae, hΔ⟩
    exact (ball_subset_closedBall.trans (closedBall_subset_closedBall
      (show r ≤ 4 * r by linarith))).trans hball
  choose W hWo hpW hWU G hG hGae hGΔ using fun p : U ↦ hloc p p.property
  let h (p : ℝ × ℝ) : ℂ := if hp : p ∈ U then G ⟨p, hp⟩ p else 0
  have heq (i : U) : EqOn h (G i) (W i) := by
    intro q hq
    have hqU := hWU i hq
    change (if hp : q ∈ U then G ⟨q, hp⟩ q else 0) = G i q
    rw [dite_eq_left hqU]
    have ha1 : G ⟨q, hqU⟩ =ᵐ[volume.restrict (W i ∩ W ⟨q, hqU⟩)] f :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hGae ⟨q, hqU⟩)
    have ha2 : G i =ᵐ[volume.restrict (W i ∩ W ⟨q, hqU⟩)] f :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hGae i)
    have hae : G ⟨q, hqU⟩ =ᵐ[volume.restrict (W i ∩ W ⟨q, hqU⟩)] G i :=
      ha1.trans ha2.symm
    exact Measure.eqOn_open_of_ae_eq hae ((hWo i).inter (hWo ⟨q, hqU⟩))
      (hG ⟨q, hqU⟩).continuous.continuousOn (hG i).continuous.continuousOn ⟨hq, hpW _⟩
  have hgerm (p : ℝ × ℝ) (hp : p ∈ U) : h =ᶠ[𝓝 p] G ⟨p, hp⟩ :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨W ⟨p, hp⟩, (hWo _).mem_nhds (hpW _), heq _⟩
  refine ⟨h, ?_, ?_, ?_⟩
  · intro p hp
    exact ((hG ⟨p, hp⟩).contDiffAt.congr_of_eventuallyEq (hgerm p hp)).contDiffWithinAt
  · intro p hp
    exact (planeLaplacian_germ_eq (hgerm p hp)).trans (hGΔ ⟨p, hp⟩ p (hpW _))
  · obtain ⟨s, hs, hcover⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover
      W hWo (fun p hp ↦ mem_iUnion_of_mem ⟨p, hp⟩ (hpW ⟨p, hp⟩))
    have hpatch (i : U) : h =ᵐ[volume.restrict (W i)] f := by
      have he : h =ᵐ[volume.restrict (W i)] G i :=
        (ae_restrict_iff' (hWo i).measurableSet).mpr
          (Eventually.of_forall fun q hq ↦ heq i hq)
      exact he.trans (hGae i)
    have ha := (ae_restrict_biUnion_iff W hs (fun p ↦ h p = f p)).mpr
      (fun i _ ↦ hpatch i)
    exact ha.filter_mono (ae_mono (Measure.restrict_mono hcover le_rfl))

end NoEmbeddedEigenvalues
