module

public import EulerDipoleEigenvalues.Analysis.FunctionSpaces.SobolevLocal
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Tests and integrability through a smooth chart

Blueprint: `lem:smooth-chart-tests`.

Compact test pullback is extended by zero outside the chart source. Its support
is contained in the inverse image of the original compact support. Constant
Jacobian transport applies to genuine integrability, not just integral values.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

local instance : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]
  infer_instance

open scoped Classical in
/-- Pull a test back through a chart, extending by zero outside its source. -/
def chartTest (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (φ : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := e.source.indicator (φ ∘ e)

lemma chartTest_eq (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (φ : ℝ × ℝ → ℂ) {q : ℝ × ℝ} (hq : q ∈ e.source) :
    chartTest e φ q = φ (e q) := indicator_of_mem hq _

/-- Smooth chart pullback gives a genuine compactly supported source test. -/
theorem isTestFunctionOn_chartTest {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (he : ContDiffOn ℝ ∞ e e.source) {φ : ℝ × ℝ → ℂ}
    (hφ : IsTestFunctionOn e.target φ) : IsTestFunctionOn e.source (chartTest e φ) := by
  classical
  let K := e.symm '' tsupport φ
  have hK : IsCompact K := hφ.hasCompactSupport.image_of_continuousOn
    (e.symm.continuousOn.mono hφ.tsupport_subset)
  have hKs : K ⊆ e.source := by
    rintro _ ⟨p, hp, rfl⟩
    exact e.map_target (hφ.tsupport_subset hp)
  have hs : tsupport (chartTest e φ) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro q hq
    by_cases hqs : q ∈ e.source
    · refine ⟨e q, ?_, e.left_inv hqs⟩
      apply subset_tsupport φ
      simpa only [Function.mem_support, chartTest_eq e φ hqs] using hq
    · exact False.elim (hq (indicator_of_notMem hqs _))
  refine ⟨contDiff_iff_contDiffAt.mpr (fun q ↦ ?_), hK.of_isClosed_subset
    (isClosed_tsupport _) hs, hs.trans hKs⟩
  by_cases hq : q ∈ e.source
  · apply (hφ.contDiff.contDiffAt.comp q
      (he.contDiffAt (e.open_source.mem_nhds hq))).congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hq] with z hz
    exact chartTest_eq e φ hz
  · have hqK : q ∉ K := fun h ↦ hq (hKs h)
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hqK] with z hz
    exact image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hs h))

/-- Local L¹ descends through a smooth chart with Jacobian two. -/
theorem locallyIntegrableOn_comp_chart_symm
    {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (he : ContDiffOn ℝ ∞ e e.source)
    (hdet : ∀ q ∈ e.source, (fderiv ℝ e q).det = 2)
    {F : ℝ × ℝ → ℂ} (hF : LocallyIntegrableOn F e.source) :
    LocallyIntegrableOn (F ∘ e.symm) e.target := by
  apply (locallyIntegrableOn_iff e.open_target.isLocallyClosed).mpr
  intro K hKs hK
  let L := e.symm '' K
  have hL : IsCompact L := hK.image_of_continuousOn (e.symm.continuousOn.mono hKs)
  have hLs : L ⊆ e.source := by
    rintro _ ⟨p, hp, rfl⟩
    exact e.map_target (hKs hp)
  have him : e '' L = K := by
    ext p
    constructor
    · rintro ⟨q, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [e.right_inv (hKs hz)] using hz
    · intro hp
      exact ⟨e.symm p, ⟨p, hp, rfl⟩, e.right_inv (hKs hp)⟩
  rw [← him]
  apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hL.measurableSet
    (fun q hq ↦ ((he.contDiffAt (e.open_source.mem_nhds (hLs hq))).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt) (e.injOn.mono hLs) _).mpr
  apply ((hF.integrableOn_compact_subset hLs hL).smul (2 : ℝ)).congr
  filter_upwards [ae_restrict_mem hL.measurableSet] with q hq
  simp only [Pi.smul_apply, Function.comp_apply, e.left_inv (hLs hq), hdet q (hLs hq), abs_of_pos
    (by norm_num : (0 : ℝ) < 2)]

/-- L² descends through the same constant-Jacobian chart. -/
theorem memLp_two_comp_chart_symm
    {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (he : ContDiffOn ℝ ∞ e e.source)
    (hdet : ∀ q ∈ e.source, (fderiv ℝ e q).det = 2)
    {F : ℝ × ℝ → ℂ} (hF : MemLp F 2 (volume.restrict e.source)) :
    MemLp (F ∘ e.symm) 2 (volume.restrict e.target) := by
  have hl : LocallyIntegrableOn F e.source :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hF.locallyIntegrable (by norm_num))
  have hm := (locallyIntegrableOn_comp_chart_symm he hdet hl).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  rw [← e.image_source_eq_target]
  apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    e.open_source.measurableSet (fun q hq ↦
      ((he.contDiffAt (e.open_source.mem_nhds hq)).differentiableAt
        (by simp)).hasFDerivAt.hasFDerivWithinAt) e.injOn _).mpr
  apply (((memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF).smul
    (2 : ℝ)).congr
  filter_upwards [ae_restrict_mem e.open_source.measurableSet] with q hq
  simp only [Pi.smul_apply, Function.comp_apply, e.left_inv hq, hdet q hq, abs_of_pos
    (by norm_num : (0 : ℝ) < 2)]

/-- Constant-Jacobian change of variables for a test-weighted integral.
No finiteness claim is inferred from this identity. -/
theorem integral_mul_test_chart {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (he : ContDiffOn ℝ ∞ e e.source)
    (hdet : ∀ q ∈ e.source, (fderiv ℝ e q).det = 2)
    (F : ℝ × ℝ → ℂ) {φ : ℝ × ℝ → ℂ} (hφ : IsTestFunctionOn e.target φ) :
    (∫ p, F p * φ p) = ∫ q in e.source, (2 : ℂ) * F (e q) * φ (e q) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp ↦ by
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hp (hφ.tsupport_subset h)), mul_zero]),
    integral_target_eq_integral_abs_det_fderiv_smul volume
      (fun q hq ↦ ((he.contDiffAt (e.open_source.mem_nhds hq)).differentiableAt
        (by simp)).hasFDerivAt)]
  apply setIntegral_congr_fun e.open_source.measurableSet
  intro q hq
  dsimp only
  rw [hdet q hq, abs_of_pos (by norm_num : (0 : ℝ) < 2), Complex.real_smul]
  push_cast
  ring

/-- Spatial a.e. equality pulls back through a nonsingular chart. The functions
need not be separately measurable: their a.e.-zero norm difference is integrable. -/
theorem ae_eq_comp_chart {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (he : ContDiffOn ℝ ∞ e e.source)
    (hdet : ∀ q ∈ e.source, (fderiv ℝ e q).det = 2)
    {F G : ℝ × ℝ → ℂ} (hFG : F =ᵐ[volume.restrict e.target] G) :
    F ∘ e =ᵐ[volume.restrict e.source] G ∘ e := by
  let N := fun p ↦ ‖F p - G p‖
  have hN : N =ᵐ[volume.restrict e.target] 0 := by
    filter_upwards [hFG] with p hp
    simp [N, hp]
  have h0 : IntegrableOn (0 : ℝ × ℝ → ℝ) e.target := integrable_zero _ _ _
  have hNi : IntegrableOn N e.target := h0.congr hN.symm
  have hder q (hq : q ∈ e.source) :=
    ((he.contDiffAt (e.open_source.mem_nhds hq)).differentiableAt (by simp)).hasFDerivAt
  have hi : IntegrableOn (fun q ↦ |(fderiv ℝ e q).det| • N (e q)) e.source := by
    apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
      e.open_source.measurableSet (fun q hq ↦ (hder q hq).hasFDerivWithinAt) e.injOn N).mp
    rwa [e.image_source_eq_target]
  have hz : (∫ q in e.source, |(fderiv ℝ e q).det| • N (e q)) = 0 := by
    rw [← integral_target_eq_integral_abs_det_fderiv_smul volume hder N,
      integral_congr_ae hN]
    simp
  have hp := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall (fun q ↦ by positivity)) hi).mp hz
  filter_upwards [hp, ae_restrict_mem e.open_source.measurableSet] with q hq hqs
  rw [hdet q hqs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hq
  change (2 : ℝ) * ‖F (e q) - G (e q)‖ = 0 at hq
  exact sub_eq_zero.mp (norm_eq_zero.mp ((mul_eq_zero.mp hq).resolve_left (by norm_num)))

end EulerDipoleEigenvalues
