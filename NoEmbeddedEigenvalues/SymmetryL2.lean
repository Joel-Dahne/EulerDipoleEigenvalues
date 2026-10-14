import NoEmbeddedEigenvalues.Setup
import Mathlib.MeasureTheory.Group.Prod

/-!
# Symmetries on L²

Measure-preserving pullbacks, their character action, and invariance of the
Fourier-defined inverse Laplacian and character-tested transport equation.
-/

noncomputable section
namespace NoEmbeddedEigenvalues

open Real Complex MeasureTheory
open scoped InnerProductSpace ComplexConjugate

instance : (volume : Measure Angle).IsAddLeftInvariant :=
  inferInstanceAs ((volume : Measure (AddCircle (2 * π))).IsAddLeftInvariant)

instance : (volume : Measure Angle).IsNegInvariant :=
  inferInstanceAs ((volume : Measure (AddCircle (2 * π))).IsNegInvariant)

/-- The character of a sum of torus points is the product of their characters. -/
theorem char_add_point (k : ℤ × ℤ) (p q : Torus) :
    char k (p + q) = char k p * char k q := by
  change AddCircle (2 * π) × AddCircle (2 * π) at p q
  change fourier k.1 (p.1 + q.1) * fourier k.2 (p.2 + q.2) =
    (fourier k.1 p.1 * fourier k.2 p.2) * (fourier k.1 q.1 * fourier k.2 q.2)
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
  ring

theorem char_neg_point (k : ℤ × ℤ) (p : Torus) : char k (-p) = char (-k) p := by
  change AddCircle (2 * π) × AddCircle (2 * π) at p
  change fourier k.1 (-p.1) * fourier k.2 (-p.2) =
    fourier (-k.1) p.1 * fourier (-k.2) p.2
  simp only [fourier_apply, smul_neg, neg_smul]

/-- The phase introduced by translation through (π,π). -/
def reflectionPhase (k : ℤ × ℤ) : ℂ := char k ((π : Angle), (π : Angle))

theorem char_comp_S₁ (k : ℤ × ℤ) (p : Torus) :
    char k (S₁ p) = reflectionPhase k * char (-k.2, -k.1) p := by
  have hp : S₁ p = ((π : Angle), (π : Angle)) + -(p.2, p.1) := by
    simp [S₁, sub_eq_add_neg]
  rw [hp]
  rw [char_add_point, char_neg_point]
  change reflectionPhase k * (fourier (-k.1) p.2 * fourier (-k.2) p.1) =
    reflectionPhase k * (fourier (-k.2) p.1 * fourier (-k.1) p.2)
  ring

theorem char_comp_S₂ (k : ℤ × ℤ) (p : Torus) :
    char k (S₂ p) = reflectionPhase k * char (k.2, k.1) p := by
  change char k (((π : Angle), (π : Angle)) + (p.2, p.1)) = _
  rw [char_add_point]
  change reflectionPhase k * (fourier k.1 p.2 * fourier k.2 p.1) =
    reflectionPhase k * (fourier k.2 p.1 * fourier k.1 p.2)
  ring

theorem char_comp_R (k : ℤ × ℤ) (p : Torus) :
    char k (R p) = char (-k.2, k.1) p := by
  change AddCircle (2 * π) × AddCircle (2 * π) at p
  change fourier k.1 p.2 * fourier k.2 (-p.1) =
    fourier (-k.2) p.1 * fourier k.1 p.2
  simp only [fourier_apply, smul_neg, neg_smul]
  ring

theorem measurePreserving_S₁ : MeasurePreserving S₁ := by
  have hm : MeasurePreserving (fun x : Angle => (π : Angle) - x) := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_left volume (π : Angle)).comp (Measure.measurePreserving_neg volume)
  convert! (hm.prod hm).comp Measure.measurePreserving_swap using 1

theorem measurePreserving_S₂ : MeasurePreserving S₂ := by
  have hm := measurePreserving_add_left (volume : Measure Angle) (π : Angle)
  convert! (hm.prod hm).comp Measure.measurePreserving_swap using 1

theorem measurePreserving_R : MeasurePreserving R := by
  convert! ((MeasurePreserving.id (volume : Measure Angle)).prod
    (Measure.measurePreserving_neg (volume : Measure Angle))).comp
    Measure.measurePreserving_swap using 1

/-- Pullback through a measure-preserving torus map, as a complex linear isometry. -/
def pullback (T : Torus → Torus) (hT : MeasurePreserving T) : L2 →ₗᵢ[ℂ] L2 :=
  Lp.compMeasurePreservingₗᵢ ℂ T hT

/-- Reflection across x+y=π on L². -/
def reflect₁ : L2 →ₗᵢ[ℂ] L2 := pullback S₁ measurePreserving_S₁
/-- Reflection across x-y=π on L². -/
def reflect₂ : L2 →ₗᵢ[ℂ] L2 := pullback S₂ measurePreserving_S₂
/-- Clockwise quarter-rotation pullback on L². -/
def rotate : L2 →ₗᵢ[ℂ] L2 := pullback R measurePreserving_R

theorem char_ne_zero (k : ℤ × ℤ) (p : Torus) : char k p ≠ 0 := by
  change AddCircle (2 * π) × AddCircle (2 * π) at p
  have hn : ‖char k p‖ = 1 := by
    change ‖fourier k.1 p.1 * fourier k.2 p.2‖ = 1
    simp only [norm_mul, fourier_apply, Circle.norm_coe, one_mul]
  intro hz
  rw [hz, norm_zero] at hn
  norm_num at hn

theorem L0char_comp_S₁ (k : ℤ × ℤ) (p : Torus) :
    L0char k (S₁ p) = reflectionPhase k * L0char (-k.2, -k.1) p := by
  have hs (a : Angle) : (π - a).sin = a.sin := by
    rw [← neg_sub, Angle.sin_neg, Angle.sin_sub_pi, neg_neg]
  change I * (k.1 * (π - p.1).sin - k.2 * (π - p.2).sin) * char k (S₁ p) =
    reflectionPhase k * (I * ((-k.2 : ℤ) * p.2.sin - (-k.1 : ℤ) * p.1.sin) *
      char (-k.2, -k.1) p)
  rw [hs, hs, char_comp_S₁]
  push_cast
  ring

theorem L0char_comp_S₂ (k : ℤ × ℤ) (p : Torus) :
    L0char k (S₂ p) = reflectionPhase k * L0char (k.2, k.1) p := by
  have hs (a : Angle) : (π + a).sin = -a.sin := by
    rw [add_comm, Angle.sin_add_pi]
  change I * (k.1 * (π + p.1).sin - k.2 * (π + p.2).sin) * char k (S₂ p) =
    reflectionPhase k * (I * (k.2 * p.2.sin - k.1 * p.1.sin) * char (k.2, k.1) p)
  rw [hs, hs, char_comp_S₂]
  push_cast
  ring

theorem L0char_comp_R (k : ℤ × ℤ) (p : Torus) :
    L0char k (R p) = L0char (-k.2, k.1) p := by
  change I * (k.1 * (-p.1).sin - k.2 * p.2.sin) * char k (R p) =
    I * ((-k.2 : ℤ) * p.2.sin - k.1 * p.1.sin) * char (-k.2, k.1) p
  rw [Angle.sin_neg, char_comp_R]
  push_cast
  ring

/-- Lift a pointwise character or transport-character transformation to L². -/
theorem pullback_toLp_eq (T : Torus → Torus) (hT : MeasurePreserving T)
    (f f' : C(Torus, ℂ)) (c : ℂ) (heq : ∀ p, f (T p) = c * f' p) :
    pullback T hT (ContinuousMap.toLp 2 volume ℂ f) =
      c • ContinuousMap.toLp 2 volume ℂ f' := by
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_compMeasurePreserving (ContinuousMap.toLp 2 volume ℂ f) hT,
    hT.quasiMeasurePreserving.ae_eq_comp
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume f),
    Lp.coeFn_smul c (ContinuousMap.toLp 2 volume ℂ f'),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume f'] with p hp hf hc hf'
  change Lp.compMeasurePreserving T hT (ContinuousMap.toLp 2 volume ℂ f) p = _
  rw [hp, hf, hc]
  change f (T p) = c * (ContinuousMap.toLp 2 volume ℂ f') p
  rw [hf']
  exact heq p

/-- Data sufficient to transport the Fourier and weak-transport equation through a symmetry. -/
structure CharacterSymmetry where
  map : Torus → Torus
  preserving : MeasurePreserving map
  frequency : (ℤ × ℤ) → ℤ × ℤ
  onto : Function.Surjective frequency
  zero_iff : ∀ k, frequency k = 0 ↔ k = 0
  normSq_eq : ∀ k, normSq (frequency k) = normSq k
  phase : (ℤ × ℤ) → ℂ
  phase_ne_zero : ∀ k, phase k ≠ 0
  char_eq : ∀ k p, char k (map p) = phase k * char (frequency k) p
  transport_eq : ∀ k p, L0char k (map p) = phase k * L0char (frequency k) p

namespace CharacterSymmetry

def action (s : CharacterSymmetry) : L2 →ₗᵢ[ℂ] L2 := pullback s.map s.preserving

theorem action_char (s : CharacterSymmetry) (k : ℤ × ℤ) :
    s.action (charLp k) = s.phase k • charLp (s.frequency k) :=
  pullback_toLp_eq s.map s.preserving _ _ _ (s.char_eq k)

theorem action_transport_char (s : CharacterSymmetry) (k : ℤ × ℤ) :
    s.action (L0charLp k) = s.phase k • L0charLp (s.frequency k) :=
  pullback_toLp_eq s.map s.preserving _ _ _ (s.transport_eq k)

theorem coefficient (s : CharacterSymmetry) (g : L2) (k : ℤ × ℤ) :
    conj (s.phase k) * fourierCoeff (s.action g) (s.frequency k) = fourierCoeff g k := by
  have hi := s.action.inner_map_map (charLp k) g
  rw [s.action_char, inner_smul_left] at hi
  unfold fourierCoeff
  rw [← hi]
  ring

theorem meanZero (s : CharacterSymmetry) {g : L2} (hg : MeanZero g) :
    MeanZero (s.action g) := by
  have hk := (s.zero_iff 0).mpr rfl
  have hc := s.coefficient g 0
  rw [hk, hg] at hc
  exact (mul_eq_zero.mp hc).resolve_left ((map_ne_zero (starRingEnd ℂ)).mpr (s.phase_ne_zero 0))

theorem invLap_commute (s : CharacterSymmetry) (g : L2) :
    s.action (invLap g) = invLap (s.action g) := by
  apply fourierCoeff_ext
  intro l
  obtain ⟨k, rfl⟩ := s.onto l
  apply mul_left_cancel₀ ((map_ne_zero (starRingEnd ℂ)).mpr (s.phase_ne_zero k))
  rw [s.coefficient, fourierCoeff_invLap, fourierCoeff_invLap]
  by_cases hk : k = 0
  · simp [hk, (s.zero_iff 0).mpr rfl]
  · simp only [hk, (s.zero_iff k).not.mpr hk, ite_false, s.normSq_eq]
    rw [← s.coefficient g k]
    ring

theorem hasL0 (s : CharacterSymmetry) {g h : L2} (hg : HasL0 g h) :
    HasL0 (s.action g) (s.action h) := by
  intro l
  obtain ⟨k, rfl⟩ := s.onto l
  apply mul_left_cancel₀ ((map_ne_zero (starRingEnd ℂ)).mpr (s.phase_ne_zero k))
  have hi := s.action.inner_map_map (charLp k) h
  have hj := s.action.inner_map_map (L0charLp k) g
  rw [s.action_char, inner_smul_left] at hi
  rw [s.action_transport_char, inner_smul_left] at hj
  rw [hi, mul_neg, hj, hg k]

theorem eigenSolution (s : CharacterSymmetry) {lam : ℝ} {g : L2}
    (hg : IsEigenSolution lam g) : IsEigenSolution lam (s.action g) := by
  refine ⟨s.meanZero hg.1, ?_⟩
  have hh := s.hasL0 hg.2
  simpa only [map_add, map_smul, s.invLap_commute] using hh

end CharacterSymmetry

/-- Reflection S₁ with its character and transport-character data. -/
def symmetry₁ : CharacterSymmetry where
  map := S₁
  preserving := measurePreserving_S₁
  frequency k := (-k.2, -k.1)
  onto := by
    rintro ⟨a, b⟩
    exact ⟨(-b, -a), by simp⟩
  zero_iff := by
    rintro ⟨a, b⟩
    change ((-b, -a) : ℤ × ℤ) = (0, 0) ↔ (a, b) = (0, 0)
    simp [and_comm]
  normSq_eq := by intro k; simp [normSq]; ring
  phase := reflectionPhase
  phase_ne_zero k := char_ne_zero k _
  char_eq := char_comp_S₁
  transport_eq := L0char_comp_S₁

/-- Reflection S₂ with its character and transport-character data. -/
def symmetry₂ : CharacterSymmetry where
  map := S₂
  preserving := measurePreserving_S₂
  frequency k := (k.2, k.1)
  onto := by
    rintro ⟨a, b⟩
    exact ⟨(b, a), rfl⟩
  zero_iff := by
    rintro ⟨a, b⟩
    change ((b, a) : ℤ × ℤ) = (0, 0) ↔ (a, b) = (0, 0)
    simp [and_comm]
  normSq_eq := by intro k; simp [normSq]; ring
  phase := reflectionPhase
  phase_ne_zero k := char_ne_zero k _
  char_eq := char_comp_S₂
  transport_eq := L0char_comp_S₂

/-- Rotation R with its character and transport-character data. -/
def rotationSymmetry : CharacterSymmetry where
  map := R
  preserving := measurePreserving_R
  frequency k := (-k.2, k.1)
  onto := by
    rintro ⟨a, b⟩
    exact ⟨(b, -a), by simp⟩
  zero_iff := by
    rintro ⟨a, b⟩
    change ((-b, a) : ℤ × ℤ) = (0, 0) ↔ (a, b) = (0, 0)
    simp [and_comm]
  normSq_eq := by intro k; simp [normSq]; ring
  phase _ := 1
  phase_ne_zero _ := one_ne_zero
  char_eq := by intro k p; simpa only [one_mul] using char_comp_R k p
  transport_eq := by intro k p; simpa only [one_mul] using L0char_comp_R k p

theorem IsEigenSolution.reflect₁ {lam : ℝ} {g : L2} (hg : IsEigenSolution lam g) :
    IsEigenSolution lam (reflect₁ g) := symmetry₁.eigenSolution hg

theorem IsEigenSolution.reflect₂ {lam : ℝ} {g : L2} (hg : IsEigenSolution lam g) :
    IsEigenSolution lam (reflect₂ g) := symmetry₂.eigenSolution hg

theorem IsEigenSolution.rotate {lam : ℝ} {g : L2} (hg : IsEigenSolution lam g) :
    IsEigenSolution lam (rotate g) := rotationSymmetry.eigenSolution hg

theorem pullback_comp_apply (T U : Torus → Torus)
    (hT : MeasurePreserving T) (hU : MeasurePreserving U) (g : L2) :
    pullback U hU (pullback T hT g) = pullback (T ∘ U) (hT.comp hU) g := by
  exact (Lp.compMeasurePreserving_comp_apply g hT hU).symm

theorem pullback_congr {T U : Torus → Torus} (hT : MeasurePreserving T)
    (hU : MeasurePreserving U) (heq : T = U) (g : L2) :
    pullback T hT g = pullback U hU g := by
  subst U
  rfl

theorem reflect₁_involutive (g : L2) : reflect₁ (reflect₁ g) = g := by
  change pullback S₁ _ (pullback S₁ _ g) = g
  rw [pullback_comp_apply]
  exact (pullback_congr _ (MeasurePreserving.id volume) S₁_comp_S₁ g).trans
    (Lp.compMeasurePreserving_id_apply g)

theorem reflect₂_involutive (g : L2) : reflect₂ (reflect₂ g) = g := by
  change pullback S₂ _ (pullback S₂ _ g) = g
  rw [pullback_comp_apply]
  exact (pullback_congr _ (MeasurePreserving.id volume) S₂_comp_S₂ g).trans
    (Lp.compMeasurePreserving_id_apply g)

theorem reflect_commute (g : L2) : reflect₁ (reflect₂ g) = reflect₂ (reflect₁ g) := by
  change pullback S₁ _ (pullback S₂ _ g) = pullback S₂ _ (pullback S₁ _ g)
  rw [pullback_comp_apply, pullback_comp_apply]
  exact pullback_congr _ _ (S₂_comp_S₁.trans S₁_comp_S₂.symm) g

theorem reflect₁_rotate (g : L2) : reflect₁ (rotate g) = rotate (reflect₂ g) := by
  change pullback S₁ _ (pullback R _ g) = pullback R _ (pullback S₂ _ g)
  rw [pullback_comp_apply, pullback_comp_apply]
  exact pullback_congr _ _ R_comp_S₁ g

theorem reflect₂_rotate (g : L2) : reflect₂ (rotate g) = rotate (reflect₁ g) := by
  change pullback S₂ _ (pullback R _ g) = pullback R _ (pullback S₁ _ g)
  rw [pullback_comp_apply, pullback_comp_apply]
  exact pullback_congr _ _ R_comp_S₂ g

end NoEmbeddedEigenvalues
