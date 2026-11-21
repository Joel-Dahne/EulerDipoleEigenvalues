import NoEmbeddedEigenvalues.Transport.WeightedForcing.RotationWeakGradient
import NoEmbeddedEigenvalues.Virial.OriginalDomain.CellPeriodization

/-!
# Rotation and linearity of spatial transport pairs

Blueprint: `lem:transport-pair-rotation`, `lem:transport-rotation-neighbourhood`.

The quarter rotation preserves the vector field, the weak equation and all
integer Sobolev orders. Domain restrictions retain the original raw fields.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter
open scoped ContDiff

/-- The dipole flow commutes with the Cartesian quarter rotation. -/
theorem rotLift_dipoleFlow (p : ℝ × ℝ) (t : ℝ) :
    rotLift (dipoleFlow p t) = dipoleFlow (rotLift p) t := by
  have he : (fun s ↦ rotLift (dipoleFlow p s)) = dipoleFlow (rotLift p) := by
    apply eq_dipoleFlow
    · rw [dipoleFlow_zero]
    · intro s
      have hd := rotLinear.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s
        (hasDerivAt_dipoleFlow p s)
      convert hd using 1 <;>
        simp [dipoleVelocity, rotLift, rotLinear, Function.comp_def]
  exact congrFun he t

/-- Pullback of an open union of orbits by rotation is an open union of orbits. -/
theorem IsOrbitUnion.preimage_rotLift {U : Set (ℝ × ℝ)} (hU : IsOrbitUnion U) :
    IsOrbitUnion (rotLift ⁻¹' U) := by
  refine ⟨hU.1.preimage (show Continuous rotLift by unfold rotLift; fun_prop), ?_⟩
  intro p hp t
  change rotLift (dipoleFlow p t) ∈ U
  rw [rotLift_dipoleFlow]
  exact hU.2 _ hp t

/-- Rotation commutes with the classical transport operator. -/
theorem classicalL0_comp_rotLift {φ : ℝ × ℝ → ℂ} (hφ : Differentiable ℝ φ)
    (p : ℝ × ℝ) :
    classicalL0 (φ ∘ rotLift) p = classicalL0 φ (rotLift p) := by
  have hx := coordPartial_comp_planeAffine hφ rotLinear 0 0 p
  have hy := coordPartial_comp_planeAffine hφ rotLinear 0 1 p
  rw [planeAffine_rotLinear] at hx hy
  have ex : partialX (φ ∘ rotLift) p = -partialY φ (rotLift p) := by
    simpa [affineCoeff, planeDirection, axisCoord,
      rotLinear, rotLift, coordPartial] using hx
  have ey : partialY (φ ∘ rotLift) p = partialX φ (rotLift p) := by
    simpa [affineCoeff, planeDirection, axisCoord,
      rotLinear, rotLift, coordPartial] using hy
  simp only [classicalL0, ex, ey, Complex.real_smul, rotLift, Real.sin_neg,
    Complex.ofReal_neg]
  ring

/-- The weak transport equation pulls back under rotation on its actual domain. -/
theorem HasWeakL0On.comp_rotLift {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {F G : ℝ × ℝ → ℂ} (h : HasWeakL0On U F G) :
    HasWeakL0On (rotLift ⁻¹' U) (F ∘ rotLift) (G ∘ rotLift) := by
  let T := planeAffine rotLinear 0
  have hm : MeasurePreserving T := by
    dsimp only [T]
    rw [planeAffine_rotLinear]
    exact measurePreserving_rotLift
  refine ⟨?_, ?_, ?_⟩
  · simpa only [planeAffine_rotLinear] using
      locallyIntegrableOn_comp_planeAffine rotLinear 0 hm hU h.1
  · simpa only [planeAffine_rotLinear] using
      locallyIntegrableOn_comp_planeAffine rotLinear 0 hm hU h.2.1
  intro φ hφ
  let ψ := φ ∘ T.symm
  have hψ : IsTestFunctionOn U ψ := by
    refine ⟨hφ.contDiff.comp (contDiff_planeAffine_symm rotLinear 0),
      hφ.hasCompactSupport.comp_homeomorph T.symm, ?_⟩
    intro p hp
    have ht : T.symm p ∈ tsupport φ := by
      change p ∈ tsupport (φ ∘ T.symm) at hp
      rwa [tsupport_comp_eq_preimage] at hp
    have hs := hφ.tsupport_subset ht
    change rotLift (T.symm p) ∈ U at hs
    have he : rotLift (T.symm p) = p := by
      simpa only [T, planeAffine_rotLinear] using T.apply_symm_apply p
    rwa [he] at hs
  have hc : ψ ∘ rotLift = φ := by
    have hcT : ψ ∘ T = φ := funext fun p ↦ congrArg φ (T.symm_apply_apply p)
    simpa only [T, planeAffine_rotLinear] using hcT
  have he (p : ℝ × ℝ) : classicalL0 ψ (rotLift p) = classicalL0 φ p := by
    rw [← classicalL0_comp_rotLift (hψ.contDiff.differentiable (by simp)), hc]
  have hw := h.2.2 ψ hψ
  rw [← hm.integral_comp T.measurableEmbedding (fun p ↦ F p * classicalL0 ψ p),
    ← hm.integral_comp T.measurableEmbedding (fun p ↦ G p * ψ p)] at hw
  simpa only [T, planeAffine_rotLinear, Function.comp_apply, he,
    show ∀ p, ψ (rotLift p) = φ p from congrFun hc] using hw

/-- Weak transport is additive, with integrability inherited from both summands. -/
theorem HasWeakL0On.add {U : Set (ℝ × ℝ)} {F G D E : ℝ × ℝ → ℂ}
    (h : HasWeakL0On U F D) (h' : HasWeakL0On U G E) :
    HasWeakL0On U (fun p ↦ F p + G p) (fun p ↦ D p + E p) := by
  convert h.sub (h'.const_mul (-1)) using 1 <;> funext p <;> ring

/-- Restrict a transport pair to a smaller open union of whole orbits. -/
theorem IsTransportPair.mono {lam : ℝ} {U V : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hV : IsOrbitUnion V) (hVU : V ⊆ U) :
    IsTransportPair lam V v f :=
  ⟨hp.ne_zero, hV, hp.memLp.mono_measure (Measure.restrict_mono_set _ hVU),
    hp.memSobolevOn.mono hVU, hp.hasWeakL0On.mono hVU⟩

/-- Rotation preserves transport pairs, without changing the real frequency. -/
theorem IsTransportPair.comp_rotLift {lam : ℝ} {U : Set (ℝ × ℝ)}
    {v f : ℝ × ℝ → ℂ} (hp : IsTransportPair lam U v f) :
    IsTransportPair lam (rotLift ⁻¹' U) (v ∘ rotLift) (f ∘ rotLift) := by
  have hm : MeasurePreserving (planeAffine rotLinear 0) := by
    rw [planeAffine_rotLinear]
    exact measurePreserving_rotLift
  refine ⟨hp.ne_zero, hp.isOrbitUnion.preimage_rotLift, ?_, ?_, ?_⟩
  · simpa only [planeAffine_rotLinear] using
      memLp_comp_planeAffine rotLinear 0 hm hp.isOrbitUnion.1.measurableSet hp.memLp
  · simpa only [planeAffine_rotLinear] using
      hp.memSobolevOn.comp_planeAffine rotLinear 0 hm hp.isOrbitUnion.1
  · exact hp.hasWeakL0On.comp_rotLift hp.isOrbitUnion.1

/-- Scalar multiples of both fields preserve the transport pair. -/
theorem IsTransportPair.const_mul {lam : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (c : ℂ) :
    IsTransportPair lam U (fun p ↦ c * v p) (fun p ↦ c * f p) := by
  refine ⟨hp.ne_zero, hp.isOrbitUnion, hp.memLp.const_mul c,
    MemSobolevOnWith.const_mul hp.memSobolevOn c, ?_⟩
  convert hp.hasWeakL0On.const_mul c using 1 <;> funext p <;> ring

/-- Addition of transport pairs on the same domain preserves their frequency. -/
theorem IsTransportPair.add {lam : ℝ} {U : Set (ℝ × ℝ)} {v f w g : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hq : IsTransportPair lam U w g) :
    IsTransportPair lam U (fun p ↦ v p + w p) (fun p ↦ f p + g p) := by
  refine ⟨hp.ne_zero, hp.isOrbitUnion, hp.memLp.add hq.memLp,
    MemSobolevOnWith.add hp.memSobolevOn hq.memSobolevOn, ?_⟩
  convert hp.hasWeakL0On.add hq.hasWeakL0On using 1 <;> funext p <;> ring

/-- Finite intersections of open unions of orbits remain such unions. -/
theorem IsOrbitUnion.inter {U V : Set (ℝ × ℝ)} (hU : IsOrbitUnion U)
    (hV : IsOrbitUnion V) : IsOrbitUnion (U ∩ V) :=
  ⟨hU.1.inter hV.1, fun p hp t ↦ ⟨hU.2 p hp.1 t, hV.2 p hp.2 t⟩⟩

/-- Rotation preserves the closed physical cell, not only its interior. -/
theorem rotLift_mem_closure_cellSquare {p : ℝ × ℝ} (hp : p ∈ closure cellSquare) :
    rotLift p ∈ closure cellSquare := by
  have hs : MapsTo rotLift cellSquare cellSquare := fun q hq ↦ (rotLift_cell_level q).1.mpr hq
  exact hs.closure_of_continuousOn
    (show Continuous rotLift by unfold rotLift; fun_prop).continuousOn hp

/-- Rotation preserves the actual saddle lattice. -/
theorem rotLift_mem_saddleSet {p : ℝ × ℝ} (hp : p ∈ saddleSet) :
    rotLift p ∈ saddleSet := by
  rcases hp with ⟨m, n, ⟨j, hj⟩, rfl⟩
  refine ⟨n, -m, ⟨j - m, by omega⟩, ?_⟩
  simp [rotLift]

/-- Four rotations suffice to choose an invariant neighbourhood of the closed
cell inside the original open union of orbits. -/
theorem exists_rotationInvariant_transport_neighbourhood {U : Set (ℝ × ℝ)}
    (hU : IsOrbitUnion U) (hb : Bornology.IsBounded U) (hcell : closure cellSquare ⊆ U) :
    ∃ V : Set (ℝ × ℝ), IsOrbitUnion V ∧ Bornology.IsBounded V ∧ V ⊆ U ∧ closure cellSquare ⊆ V ∧
      rotLift ⁻¹' V = V := by
  let V := U ∩ (rotLift ⁻¹' U ∩ (rotLift ⁻¹' (rotLift ⁻¹' U) ∩
    rotLift ⁻¹' (rotLift ⁻¹' (rotLift ⁻¹' U))))
  refine ⟨V, hU.inter (hU.preimage_rotLift.inter
    (hU.preimage_rotLift.preimage_rotLift.inter
      hU.preimage_rotLift.preimage_rotLift.preimage_rotLift)),
    hb.subset inter_subset_left, inter_subset_left, ?_, ?_⟩
  · intro p hp
    have h1 := rotLift_mem_closure_cellSquare hp
    have h2 := rotLift_mem_closure_cellSquare h1
    have h3 := rotLift_mem_closure_cellSquare h2
    exact ⟨hcell hp, hcell h1, hcell h2, hcell h3⟩
  · ext p
    simp only [V, mem_preimage, mem_inter_iff, rotLift, neg_neg]
    tauto

end NoEmbeddedEigenvalues
