import NoEmbeddedEigenvalues.QuarterMeasureTransport
import NoEmbeddedEigenvalues.WeakQuarterReconstruction
import NoEmbeddedEigenvalues.SeparatrixTraces

/-!
# Joint almost-everywhere rotation identities on recentered quarters

Blueprint: `lem:quarter-rotation-character`.

First transfer measurable spatial a.e. identities by coarea, then use the
joint measurability of both raw pullbacks. No values on an exceptional orbit
or jointly measurable family of ACL representatives are selected.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- A spatial a.e. identity of measurable raw functions holds jointly a.e.
on a base-quarter strip. -/
theorem ae_eq_comp_quarterOrbitStrip {b : ℝ} (hb : b ≤ 1)
    {F G : ℝ × ℝ → ℂ} (hF : Measurable F) (hG : Measurable G)
    (heq : F =ᵐ[volume] G) :
    (fun q ↦ F (dipoleOrbit q.1 q.2)) =ᵐ[volume.restrict (quarterOrbitStrip b)]
      (fun q ↦ G (dipoleOrbit q.1 q.2)) := by
  apply ae_eq_quarterStrip_of_ae_sections
    (hF.comp continuous_dipoleOrbit.measurable).aestronglyMeasurable
    (hG.comp continuous_dipoleOrbit.measurable).aestronglyMeasurable
  have hsec := ae_level_of_ae_cellSquare (measurableSet_eq_fun hF hG)
    (ae_restrict_of_ae heq)
  have hsub : Ioo (0 : ℝ) b ⊆ Ioo 0 1 := fun _ hh ↦ ⟨hh.1, hh.2.trans_le hb⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hsec,
    ae_restrict_mem measurableSet_Ioo] with h hh hI
  have hL := eighthPeriod_pos hI.1 (hI.2.trans_le hb)
  apply ae_restrict_of_ae_restrict_of_subset (t := Ico (-2 * eighthPeriod h)
    (6 * eighthPeriod h)) ?_ hh
  intro t ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Iteration retains the raw lift's spatial a.e. rotation character. -/
theorem liftL2_iterate_rotLift_ae {ω : L2} {κ : Bool}
    (hκ : InRotationCharacter κ ω) (k : ℕ) :
    ∀ᵐ p, liftL2 ω (rotLift^[k] p) = paritySign κ ^ k * liftL2 ω p := by
  induction k with
  | zero => exact Eventually.of_forall fun p ↦ by simp
  | succ k ih =>
    have hi := measurePreserving_rotLift.quasiMeasurePreserving.ae ih
    filter_upwards [hi, liftL2_rotLift_ae hκ] with p hp hrot
    rw [Function.iterate_succ_apply, hp, hrot, pow_succ]
    ring

/-- Each separately recentered raw quarter profile is the base profile times
its constant character, jointly a.e. rather than only on individual orbits. -/
theorem liftL2_recenteredQuarterMap_ae {b : ℝ} (hb : b ≤ 1)
    {ω : L2} {κ : Bool} (hκ : InRotationCharacter κ ω) (k : Fin 4) :
    (fun q ↦ liftL2 ω (recenteredQuarterMap k q))
      =ᵐ[volume.restrict (quarterOrbitStrip b)]
    (fun q ↦ paritySign κ ^ k.val * liftL2 ω (dipoleOrbit q.1 q.2)) := by
  have hm : Measurable (liftL2 ω) :=
    (Lp.stronglyMeasurable ω).measurable.comp
      isOpenQuotientMap_torusProj.continuous.measurable
  have hR : Measurable rotLift := by unfold rotLift; fun_prop
  exact ae_eq_comp_quarterOrbitStrip hb (hm.comp (hR.iterate k.val))
    (measurable_const.mul hm) (liftL2_iterate_rotLift_ae hκ k.val)

end NoEmbeddedEigenvalues
