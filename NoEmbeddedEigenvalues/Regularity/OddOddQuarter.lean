import NoEmbeddedEigenvalues.Regularity.OddOddMidpoint

/-!
# The base-quarter weak level derivative of odd–odd vorticity

Blueprint: `lem:dd-quarter-level`.

The logarithmic midpoint data control the transport unknown's level derivative.
The weighted forcing energy controls the forcing-level derivative on a smaller
strip. Their linear combination differentiates the actual vorticity pullback;
no raw representative is evaluated on a distinguished orbit.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set

/-- The base-quarter vorticity pullback has a specified square-integrable weak
level derivative (`lem:dd-quarter-level`). -/
theorem dd_quarter_level {lam : ℝ} (hlam : lam ≠ 0) {ω : L2}
    (hω : IsEigenSolution lam ω) (hs : InSector false false ω)
    {κ : Bool} (hκ : InRotationCharacter κ ω) :
    ∃ b : ℝ, 0 < b ∧ b < 1 / 2 ∧ ∃ H : ℝ × ℝ → ℂ,
      HasWeakPartialOn (quarterOrbitStrip b) 0
        (fun q ↦ liftL2 ω (dipoleOrbit q.1 q.2)) H ∧
      MemLp H 2 (volume.restrict (quarterOrbitStrip b)) := by
  obtain ⟨h₀, _, hh₀half, d, _, h₁, hh₁, hh₁₀, _, Q, Q₁, _, _, _, _, _, _, hZ, hH, _⟩ :=
    dd_log_midpoint hlam hω hs hκ
  obtain ⟨δ, hδ, _, hG⟩ := d.forcing_level_memLp
  let b := min h₁ (δ / 2)
  have hb : 0 < b := lt_min hh₁ (half_pos hδ)
  have hb₁ : b ≤ h₁ := min_le_left _ _
  have hbδ : b ≤ δ := (min_le_right _ _).trans (half_le_self hδ.le)
  have hb₀ : b ≤ h₀ := hb₁.trans hh₁₀.le
  have hsub₁ : quarterOrbitStrip b ⊆ quarterOrbitStrip h₁ := fun _ hq ↦
    ⟨hq.1, hq.2.1.trans_le hb₁, hq.2.2⟩
  have hsub₀ : quarterOrbitStrip b ⊆ quarterOrbitStrip h₀ := fun _ hq ↦
    ⟨hq.1, hq.2.1.trans_le hb₀, hq.2.2⟩
  have hweak := ((hZ.mono hsub₁).const_mul (-(lam : ℂ))).add
    ((d.forcing_level_weak.mono hsub₀).const_mul (-1))
  have heq : (fun q : ℝ × ℝ ↦
      -(lam : ℂ) * transportUnknown lam (liftL2 ω) (contStream ω) (dipoleOrbit q.1 q.2) +
        (-1 : ℂ) * contStream ω (dipoleOrbit q.1 q.2)) =
      (fun q ↦ liftL2 ω (dipoleOrbit q.1 q.2)) := by
    funext q
    unfold transportUnknown
    field_simp [Complex.ofReal_ne_zero.mpr hlam]
    ring
  rw [heq] at hweak
  exact ⟨b, hb, hb₀.trans_lt hh₀half, _, hweak,
    ((hH.mono_measure (Measure.restrict_mono hsub₁ le_rfl)).const_mul (-(lam : ℂ))).add
      ((hG b hb₀ hbδ).const_mul (-1))⟩

end NoEmbeddedEigenvalues
