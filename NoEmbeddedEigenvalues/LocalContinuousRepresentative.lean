import NoEmbeddedEigenvalues.LocalToGlobal
import NoEmbeddedEigenvalues.SobolevTorus

/-!
# Continuous representatives of local H² functions

Blueprint: `lem:local-h2-continuous-representative`.

Compact localization on injective torus patches gives continuous local
representatives. A.e. uniqueness on open overlaps glues their actual values;
a countable subcover separately supplies agreement with the raw function.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped Topology ContDiff

private theorem injOn_torusProj_ball_one (p : ℝ × ℝ) :
    InjOn torusProj (Metric.ball p 1) := by
  have hc {a x y : ℝ} (hx : |x - a| < 1) (hy : |y - a| < 1)
      (he : (x : Real.Angle) = y) : x = y := by
    have hpi := Real.two_le_pi
    have hx' : x ∈ Ioc (a - Real.pi) (a - Real.pi + 2 * Real.pi) := by
      rw [abs_lt] at hx
      constructor <;> linarith
    have hy' : y ∈ Ioc (a - Real.pi) (a - Real.pi + 2 * Real.pi) := by
      rw [abs_lt] at hy
      constructor <;> linarith
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc hx' hy').mp he
  intro x hx y hy he
  have hx' : |x.1 - p.1| < 1 ∧ |x.2 - p.2| < 1 := by
    simpa [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff] using hx
  have hy' : |y.1 - p.1| < 1 ∧ |y.2 - p.2| < 1 := by
    simpa [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff] using hy
  exact Prod.ext (hc hx'.1 hy'.1 (congrArg Prod.fst he))
    (hc hx'.2 hy'.2 (congrArg Prod.snd he))

private theorem exists_continuous_patch_of_memSobolevLocOn_two
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {f : ℝ × ℝ → ℂ}
    (hf : MemSobolevLocOn 2 U f) {p : ℝ × ℝ} (hp : p ∈ U) :
    ∃ W : Set (ℝ × ℝ), ∃ G : ℝ × ℝ → ℂ,
      IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ ContinuousOn G W ∧ f =ᵐ[volume.restrict W] G := by
  let V := U ∩ Metric.ball p 1
  have hV : IsOpen V := hU.inter Metric.isOpen_ball
  have hpV : p ∈ V := ⟨hp, Metric.mem_ball_self (by norm_num)⟩
  obtain ⟨θ, hθs, hθc, hθd, _, hθp⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (hV.mem_nhds hpV)
  have hχ : IsTestFunctionOn V (fun q ↦ (θ q : ℂ)) :=
    ⟨Complex.ofRealCLM.contDiff.comp hθd,
      hθc.comp_left Complex.ofReal_zero,
      (tsupport_comp_subset Complex.ofReal_zero θ).trans hθs⟩
  have hfV : MemSobolevLocOn 2 V f := fun A hA hc hAV ↦ hf A hA hc
    (hAV.trans inter_subset_left)
  obtain ⟨u, hu, he, _⟩ := exists_memSobolev_periodize hV
    ((injOn_torusProj_ball_one p).mono inter_subset_right) hfV hχ
  let H := fun q ↦ continuousRep u (torusProj q)
  have hH : Continuous H := (continuousRep u).continuous.comp
    isOpenQuotientMap_torusProj.continuous
  have heH : (fun q ↦ (θ q : ℂ) * f q) =ᵐ[volume.restrict V] H := by
    filter_upwards [he, ae_restrict_of_ae (ae_torusProj (coeFn_eq_continuousRep hu))]
      with q hq huq
    exact hq.symm.trans huq
  let W := V ∩ {q | θ q ≠ 0}
  have hW : IsOpen W := hV.inter (isOpen_ne_fun hθd.continuous continuous_const)
  have hG : ContinuousOn (fun q ↦ H q / (θ q : ℂ)) W :=
    hH.continuousOn.div (Complex.continuous_ofReal.comp hθd.continuous).continuousOn
      (fun q hq ↦ Complex.ofReal_ne_zero.mpr hq.2)
  refine ⟨W, fun q ↦ H q / (θ q : ℂ), hW, ⟨hpV, by simp [hθp]⟩,
    inter_subset_left.trans inter_subset_left, hG, ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (show W ⊆ V from inter_subset_left) heH,
    ae_restrict_mem hW.measurableSet] with q heq hq
  rw [← heq, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hq.2)]

/-- Local H² data on an arbitrary open planar set have a genuine continuous
representative there, with a.e. agreement on exactly that original domain. -/
theorem exists_continuousOn_rep_of_memSobolevLocOn_two
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) {f : ℝ × ℝ → ℂ}
    (hf : MemSobolevLocOn 2 U f) :
    ∃ g : ℝ × ℝ → ℂ, ContinuousOn g U ∧ f =ᵐ[volume.restrict U] g := by
  classical
  choose W G hW hpW hWU hG he using
    (fun p : U ↦ exists_continuous_patch_of_memSobolevLocOn_two hU hf p.property)
  have hcompat (p q : U) : EqOn (G p) (G q) (W p ∩ W q) := by
    have hep : f =ᵐ[volume.restrict (W p ∩ W q)] G p :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (he p)
    have heq : f =ᵐ[volume.restrict (W p ∩ W q)] G q :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (he q)
    exact Measure.eqOn_open_of_ae_eq (hep.symm.trans heq)
      ((hW p).inter (hW q)) ((hG p).mono inter_subset_left) ((hG q).mono inter_subset_right)
  let g := fun x ↦ if hx : x ∈ U then G ⟨x, hx⟩ x else 0
  have hgW (p : U) : EqOn g (G p) (W p) := by
    intro x hx
    have hxU := hWU p hx
    dsimp only [g]
    rw [dite_eq_left hxU]
    exact hcompat ⟨x, hxU⟩ p ⟨hpW ⟨x, hxU⟩, hx⟩
  refine ⟨g, ?_, ?_⟩
  · intro x hx
    let p : U := ⟨x, hx⟩
    apply ContinuousAt.continuousWithinAt
    apply ((hG p).continuousAt ((hW p).mem_nhds (hpW p))).congr_of_eventuallyEq
    exact eventually_of_mem ((hW p).mem_nhds (hpW p)) fun y hy ↦ hgW p hy
  · have hcover : U ⊆ ⋃ p : U, W p := fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hpW ⟨x, hx⟩⟩
    obtain ⟨s, hs, hsub⟩ :=
      (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover W hW hcover
    have hlocal (p : U) : f =ᵐ[volume.restrict (W p)] g := by
      filter_upwards [he p, ae_restrict_mem (hW p).measurableSet] with x hx hxW
      exact hx.trans (hgW p hxW).symm
    exact ae_restrict_of_ae_restrict_of_subset hsub
      ((ae_restrict_biUnion_iff W hs (fun x ↦ f x = g x)).mpr (fun p _ ↦ hlocal p))

end NoEmbeddedEigenvalues
