import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The du Bois-Reymond lemma on an interval

Blueprint: `lem:du-bois-reymond` (stated).

If `∫ φ m = ∫ φ' G` for every smooth `φ` with compact support in `(α, β)`, then `G' = -m` in
the sense of distributions, so `G(h) - G(h') = ∫_h^{h'} m` for all `h < h'` outside a null set.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set
open scoped ContDiff

/-- The du Bois-Reymond lemma (`lem:du-bois-reymond`): a locally integrable `G` whose
    distributional derivative is `-m` agrees almost everywhere with a primitive of `-m`. -/
theorem exists_null_sub_eq_intervalIntegral {m G : ℝ → ℝ} {α β : ℝ}
    (hm : ∀ a b, α < a → b < β → IntegrableOn m (Icc a b))
    (hG : ∀ a b, α < a → b < β → IntegrableOn G (Icc a b))
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → ∀ a b, α < a → b < β →
      (∀ s, φ s ≠ 0 → a ≤ s ∧ s ≤ b) → ∫ s, φ s * m s = ∫ s, deriv φ s * G s) :
    ∃ N : Set ℝ, volume N = 0 ∧ ∀ h h' : ℝ, α < h → h < h' → h' < β → h ∉ N → h' ∉ N →
      ∫ s in h..h', m s = G h - G h' := by
  sorry

end NoEmbeddedEigenvalues
