import NoEmbeddedEigenvalues.Analysis.LocalSobolev.LocalContinuousRepresentative
import NoEmbeddedEigenvalues.Transport.WeightedGains.SmoothTransportPairs
import NoEmbeddedEigenvalues.Transport.WeightedGains.SaddleValueInterpolation
import NoEmbeddedEigenvalues.Transport.WeightedGains.ZeroSaddleTransportGain

/-!
# First transport gain without a saddle-value hypothesis

Blueprint: `lem:transport-first-gain`.

Interpolate the original continuous forcing's four saddle values by a smooth
quadratic profile. Its generated transport pair has a finite first weighted
mass. Subtract that pair on the original domain, apply the zero-saddle gain,
and add back the correction. No elliptic relation or parity is assumed.
-/

noncomputable section
namespace NoEmbeddedEigenvalues
open MeasureTheory Set Filter

/-- First transport gain on the positive cell (`lem:transport-first-gain`). -/
theorem transport_first_gain {lam : ℝ} {U : Set (ℝ × ℝ)} {v f : ℝ × ℝ → ℂ}
    (hp : IsTransportPair lam U v f) (hb : Bornology.IsBounded U)
    (hcell : closure cellSquare ⊆ U) :
    MemLp (fun p ↦ v p / (saddleDist p : ℂ)) 2 (volume.restrict cellSquare) := by
  obtain ⟨g, hg, hfg⟩ := exists_continuousOn_rep_of_memSobolevLocOn_two
    hp.isOrbitUnion.1 hp.memSobolevOn.memSobolevLocOn
  obtain ⟨P, hP, hPg⟩ := exists_smooth_saddle_interpolant g
  obtain ⟨w, k, hpk, _, hk, hks, hw⟩ := exists_smooth_transport_pair
    hp.ne_zero hp.isOrbitUnion hb hP
  have hrem : IsTransportPair lam U (fun p ↦ v p - w p) (fun p ↦ f p - k p) := by
    convert hp.add (hpk.const_mul (-1)) using 1 <;> funext p <;> ring
  have heq : (fun p ↦ f p - k p) =ᵐ[volume.restrict U] (fun p ↦ g p - k p) := by
    filter_upwards [hfg] with p hp
    rw [hp]
  have hz : ∀ p ∈ saddleSet, p ∈ closure cellSquare → g p - k p = 0 := by
    intro p hp hpc
    rw [hks p hp, hPg p hp hpc, sub_self]
  have hr := transport_first_gain_zero hrem hb hcell
    (hg.sub hk.continuous.continuousOn) heq hz
  have hwc := hw.mono_measure (Measure.restrict_mono_set _ (subset_closure.trans hcell))
  apply (hr.add hwc).ae_eq
  exact Eventually.of_forall fun p ↦ by
    change (v p - w p) / (saddleDist p : ℂ) + w p / (saddleDist p : ℂ) = _
    rw [← add_div, sub_add_cancel]

end NoEmbeddedEigenvalues
