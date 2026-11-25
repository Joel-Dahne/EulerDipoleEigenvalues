module

public import EulerDipoleEigenvalues.Transport.WeightedForcing.OddOddEdgeTraces
public import EulerDipoleEigenvalues.Transport.WeightedForcing.RegularEdgeCover
public import EulerDipoleEigenvalues.Analysis.LocalSobolev.TraceWindowRestriction

/-!
# Canonical zero traces of odd–odd H¹ vorticity on an absolute-level collar

Blueprint: `lem:odd-odd-collar-zero-traces`.

Reflection in any diagonal zero line reverses the dipole and acts by minus one
on the raw vorticity a.e. An admissible closed rectangle and its reflection
have a symmetric rectangular union still inside the same collar. Ordinary H¹
there supplies a canonical trace equal to its own negative. Restriction retains
zero on the original window, even when the normal point is an endpoint.
-/

@[expose] public section

noncomputable section
namespace EulerDipoleEigenvalues
open MeasureTheory Set Filter Real

/-- Local physical H¹ gives actual finite H¹ on a diagonal rectangle whose
closed image is contained in the open physical domain. -/
theorem MemSobolevLocOn.diagonal_trace_rectangle {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) {F : ℝ × ℝ → ℂ} (hF : MemSobolevLocOn 1 U F)
    (j : Fin 2) {l r a b : ℝ}
    (hsub : diagonalTraceChart j '' (Icc l r ×ˢ Icc a b) ⊆ U) :
    MemSobolevOn 1 (Ioo l r ×ˢ Ioo a b) (F ∘ diagonalTraceChart j) := by
  have hK : IsCompact (diagonalTraceChart j '' (Icc l r ×ˢ Icc a b)) :=
    (isCompact_Icc.prod isCompact_Icc).image (continuous_diagonalTraceChart j)
  obtain ⟨V, hV, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hsub
  apply ((hF V hV hVc hVU).comp_diagonalTraceChart hV j).mono
  intro q hq
  exact hKV ⟨q, ⟨Ioo_subset_Icc_self hq.1, Ioo_subset_Icc_self hq.2⟩, rfl⟩

/-- Every lifted diagonal zero line gives the same torus reflection, not just
the four edges of the central cell. -/
theorem torusProj_diagonalTraceChart_reflection_of_cos_eq_zero (j : Fin 2)
    {t : ℝ} (ht : cos t = 0) (q : ℝ × ℝ) :
    torusProj (diagonalTraceChart j (normalReflection (2 * t) q)) =
      (if j = 0 then S₁ else S₂) (torusProj (diagonalTraceChart j q)) := by
  have hc : ((2 * t : ℝ) : Angle) = (π : Angle) := by
    obtain ⟨k, hk⟩ := cos_eq_zero_iff.mp ht
    apply Angle.angle_eq_iff_two_pi_dvd_sub.mpr
    exact ⟨k, by rw [hk]; ring⟩
  fin_cases j
  · change torusProj (diagInv ((normalReflection (2 * t) q).2,
        (normalReflection (2 * t) q).1)) = S₁ (torusProj (diagInv (q.2, q.1)))
    ext <;> simp only [normalReflection_apply, diagInv_apply, torusProj, S₁,
      Angle.coe_add, Angle.coe_sub, hc] <;> abel
  · change torusProj (diagInv (normalReflection (2 * t) q)) = S₂ (torusProj (diagInv q))
    ext
    · simp only [normalReflection_apply, diagInv_apply, torusProj, S₂,
        Angle.coe_add, Angle.coe_sub, hc]
      abel
    · simp only [normalReflection_apply, diagInv_apply, torusProj, S₂,
        Angle.coe_add, Angle.coe_sub, hc]
      simp only [sub_eq_add_neg, neg_add_rev, neg_neg, Angle.neg_coe_pi]
      abel

/-- Odd parity transports to the actual pullback at every lifted diagonal zero line. -/
theorem liftL2_diagonalTraceChart_reflection_of_cos_eq_zero_ae {ω : L2}
    (hs : InSector false false ω) (j : Fin 2) {t : ℝ} (ht : cos t = 0) :
    ∀ᵐ q : ℝ × ℝ, liftL2 ω (diagonalTraceChart j (normalReflection (2 * t) q)) =
      -liftL2 ω (diagonalTraceChart j q) := by
  filter_upwards [liftL2_diagonalTraceChart_reflection_ae hs j true] with q hq
  have he : torusProj (diagonalTraceChart j (normalReflection (2 * t) q)) =
      torusProj (diagonalTraceChart j (normalReflection (2 * cellEdgeNormal true) q)) :=
    (torusProj_diagonalTraceChart_reflection_of_cos_eq_zero j ht q).trans
      (torusProj_diagonalTraceChart_reflection j true q).symm
  change ω (torusProj (diagonalTraceChart j (normalReflection (2 * t) q))) = _
  rw [he]
  exact hq

/-- The reflected rectangle stays in the same absolute-level collar. -/
theorem dipoleLift_diagonalTraceChart_reflection (j : Fin 2) {t : ℝ}
    (ht : cos t = 0) (q : ℝ × ℝ) :
    dipoleLift (diagonalTraceChart j (normalReflection (2 * t) q)) =
      -dipoleLift (diagonalTraceChart j q) := by
  simp only [dipoleLift_diagonalTraceChart, normalReflection_apply]
  simp [cos_sub, cos_two_mul, sin_two_mul, ht]

/-- Ordinary H¹ and odd parity imply every original canonical zero-trace
clause on the whole collar, including both normal endpoints. -/
theorem MemSobolevLocOn.oddOdd_collar_zero_traces {ω : L2}
    (hs : InSector false false ω) {ε : ℝ}
    (hF : MemSobolevLocOn 1 {p | |dipoleLift p| < ε} (liftL2 ω)) :
    HasZeroSeparatrixTraceOn {p | |dipoleLift p| < ε} (liftL2 ω) := by
  intro j l r a b t hlr hab ht hcos hsub
  let R := max (t - a) (b - t)
  have hRa : t - a ≤ R := le_max_left _ _
  have hRb : b - t ≤ R := le_max_right _ _
  have hR : 0 < R := by linarith
  have hA : t - R ≤ a := by linarith
  have hB : b ≤ t + R := by linarith
  have hen : ∀ y ∈ Icc (t - R) (t + R), y ∈ Icc a b ∨ 2 * t - y ∈ Icc a b := by
    intro y hy
    dsimp [R] at hy
    rcases le_total (t - a) (b - t) with h | h
    · rw [max_eq_right h] at hy
      by_cases hya : a ≤ y
      · exact Or.inl ⟨hya, by linarith [hy.2]⟩
      · exact Or.inr ⟨by linarith [ht.1], by linarith [hy.1]⟩
    · rw [max_eq_left h] at hy
      by_cases hyb : y ≤ b
      · exact Or.inl ⟨by linarith [hy.1], hyb⟩
      · exact Or.inr ⟨by linarith [hy.2], by linarith [ht.2]⟩
  have hsubS : diagonalTraceChart j '' (Icc l r ×ˢ Icc (t - R) (t + R)) ⊆
      {p | |dipoleLift p| < ε} := by
    rintro _ ⟨q, hq, rfl⟩
    rcases hen q.2 hq.2 with hqN | hqN
    · exact hsub ⟨q, ⟨hq.1, hqN⟩, rfl⟩
    · have h := hsub ⟨normalReflection (2 * t) q, ⟨by
        simpa only [normalReflection_apply] using hq.1, by
        simpa only [normalReflection_apply] using hqN⟩, rfl⟩
      change |dipoleLift (diagonalTraceChart j (normalReflection (2 * t) q))| < ε at h
      rwa [dipoleLift_diagonalTraceChart_reflection j hcos q, abs_neg] at h
  have hC : IsOpen {p | |dipoleLift p| < ε} :=
    isOpen_lt (show Continuous dipoleLift by unfold dipoleLift; fun_prop).abs continuous_const
  have hS := hF.diagonal_trace_rectangle hC j hsubS
  have hAB : t - R < t + R := by linarith
  have htS : t ∈ Icc (t - R) (t + R) := ⟨by linarith, by linarith⟩
  obtain ⟨D, hd, hD⟩ := hS.2 1
  obtain ⟨G, hm, hGF, hGD, _, _⟩ := hd.exists_l2_trace isOpen_Ioo ordConnected_Ioo
    (nonempty_Ioo.mpr hlr) hAB hS.1 hD
  have hG := hS.1.ae_eq hGF.symm
  let T := aclTrace (t - R) (t + R) G D t
  have hT : HasTransverseH1Trace l r (t - R) (t + R) t (diagonalTraceChart j)
      (liftL2 ω) T := ⟨hlr, hAB, htS, G, D, hm, hGF, hG, hD, hGD, EventuallyEq.rfl⟩
  have hTR : HasTransverseH1Trace l r (2 * t - (t + R)) (2 * t - (t - R))
      (2 * t - t) (diagonalTraceChart j) (liftL2 ω) T := by
    simpa only [show 2 * t - (t + R) = t - R by ring,
      show 2 * t - (t - R) = t + R by ring, show 2 * t - t = t by ring] using hT
  have he := hT.ae_eq_reflected hTR (χ := -1) (by
    filter_upwards [ae_restrict_of_ae
      (liftL2_diagonalTraceChart_reflection_of_cos_eq_zero_ae hs j hcos)] with q hq
    simp only [Function.comp_apply, hq, neg_one_mul, neg_neg])
  have hzero : T =ᵐ[volume.restrict (Ioo l r)] (fun _ ↦ 0) := by
    filter_upwards [he] with s hs
    simp only [neg_one_mul] at hs
    linear_combination (1 / 2 : ℂ) * hs
  have hT0 : HasTransverseH1Trace l r (t - R) (t + R) t (diagonalTraceChart j)
      (liftL2 ω) (fun _ ↦ 0) :=
    ⟨hlr, hAB, htS, G, D, hm, hGF, hG, hD, hGD, hzero.symm⟩
  obtain ⟨_, _, _, H, E, _, hHF, hH, hE, hHE, hHT⟩ := hT0.restrict_normal hA hB hab ht
  exact ⟨H, E, hHF, hH, hE, hHE, hHT.symm⟩

end EulerDipoleEigenvalues
