module

public import EulerDipoleEigenvalues.Analysis.LocalSobolev.DiagonalACL
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.StreamElliptic

/-! # Diagonal coordinate change for higher weak derivatives -/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues

open MeasureTheory Set

/-- Integer-order Sobolev regularity pulls back to diagonal coordinates. -/
theorem MemSobolevOn.comp_diagInv_order {k : ℕ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {F : ℝ × ℝ → ℂ} (hF : MemSobolevOn k U F) :
    MemSobolevOn k (diagInv ⁻¹' U) (F ∘ diagInv) := by
  induction k generalizing F with
  | zero => exact memLp_comp_diagInv hU.measurableSet hF
  | succ k ih =>
    obtain ⟨X, hx, hX⟩ := hF.2 0
    obtain ⟨Y, hy, hY⟩ := hF.2 1
    refine ⟨memLp_comp_diagInv hU.measurableSet hF.1, ?_⟩
    intro j
    fin_cases j
    · exact ⟨_, hx.comp_diagInv_fst hU hy, (ih hX).add (ih hY)⟩
    · exact ⟨_, hx.comp_diagInv_snd hU hy, by
        simpa only [sub_eq_add_neg, neg_one_mul, Function.comp_def] using
          (ih hX).add ((ih hY).const_mul (-1))⟩

/-- Local regularity pulls back without enlarging the open set. -/
theorem MemSobolevLocOn.comp_diagInv {k : ℕ} {U : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → ℂ} (hF : MemSobolevLocOn k U F) :
    MemSobolevLocOn k (diagInv ⁻¹' U) (F ∘ diagInv) := by
  intro V hV hc hVU
  let e := diagInv.toHomeomorph
  have ho : IsOpen (e '' V) := e.isOpenMap V hV
  have he : e '' closure V = closure (e '' V) := e.image_closure V
  have hK := hF _ ho (he ▸ hc.image e.continuous)
    (by rw [← he]; exact image_subset_iff.mpr hVU)
  simpa only [show (diagInv : (ℝ × ℝ) → ℝ × ℝ) = e from rfl, e.injective.preimage_image]
    using hK.comp_diagInv_order ho

/-- The determinant of the inverse diagonal chart is nonzero. -/
theorem quasiMeasurePreserving_diagInv :
    QuasiMeasurePreserving (diagInv : (ℝ × ℝ) → ℝ × ℝ) volume volume := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  exact Measure.LinearMap.quasiMeasurePreserving volume (diagInvLinear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))
    (by rw [det_diagInvLinear]; norm_num)

/-- The diagonal Laplacian of the stream is twice the lifted vorticity. -/
theorem contStream_diagInv_weak_poisson {ω : L2} (hω : MeanZero ω)
    (U : Set (ℝ × ℝ)) :
    ∃ D, HasWeakJetOn 2 U (contStream ω ∘ diagInv) D ∧
      ∀ᵐ q ∂(volume.restrict U),
        D [0, 0] q + D [1, 1] q = 2 * liftL2 ω (diagInv q) := by
  let S := streamJet2 ω
  have hS := streamJet2_weak ω (univ : Set (ℝ × ℝ))
  have hd {G : ℝ × ℝ → ℂ} (w : List (Fin 2)) (hw : w.length < 2)
      (hg : G = S w) (j : Fin 2) :
      HasWeakPartialOn U j (G ∘ diagInv)
        (fun q ↦ S (0 :: w) (diagInv q) +
          (if j = 0 then 1 else -1) * S (1 :: w) (diagInv q)) := by
    subst G
    have hx := hS.2 w hw 0
    have hy := hS.2 w hw 1
    have hsub : U ⊆ diagInv ⁻¹' (univ : Set (ℝ × ℝ)) := by simp
    fin_cases j
    · change HasWeakPartialOn U 0 _ _
      simpa [S, Function.comp_def] using (hx.comp_diagInv_fst isOpen_univ hy).mono hsub
    · change HasWeakPartialOn U 1 _ _
      simpa [S, sub_eq_add_neg, Function.comp_def] using
        (hx.comp_diagInv_snd isOpen_univ hy).mono hsub
  let D (w : List (Fin 2)) (q : ℝ × ℝ) : ℂ := match w with
    | [] => contStream ω (diagInv q)
    | j :: [] => S [0] (diagInv q) + (if j = 0 then 1 else -1) * S [1] (diagInv q)
    | i :: j :: _ =>
        (S [0, 0] (diagInv q) + (if i = 0 then 1 else -1) * S [1, 0] (diagInv q)) +
          (if j = 0 then 1 else -1) *
            (S [0, 1] (diagInv q) + (if i = 0 then 1 else -1) * S [1, 1] (diagInv q))
  refine ⟨D, ⟨rfl, ?_⟩, ?_⟩
  · intro w hw i
    rcases w with _ | ⟨j, w⟩
    · exact hd [] (by decide) hS.1.symm i
    cases w with
    | nil =>
      simpa only [D, Function.comp_apply] using
        (hd [0] (by decide) rfl i).add
          ((hd [1] (by decide) rfl i).const_mul (if j = 0 then 1 else -1))
    | cons k w => simp at hw
  · filter_upwards [ae_restrict_of_ae (quasiMeasurePreserving_diagInv.ae
      (streamJet2_laplacian hω))] with q hq
    change S [0, 0] (diagInv q) + S [1, 1] (diagInv q) = _ at hq
    simp only [D, ite_true, one_ne_zero, ite_false, one_mul, neg_one_mul]
    linear_combination 2 * hq

end EulerDipoleEigenvalues
