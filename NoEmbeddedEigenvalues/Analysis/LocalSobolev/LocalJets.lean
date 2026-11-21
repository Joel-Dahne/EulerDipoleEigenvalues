import NoEmbeddedEigenvalues.Analysis.FunctionSpaces.SobolevLocal

/-!
# Plane geometry and specified weak jets

Euclidean radius is explicit: the norm on the product of two real normed spaces
is the maximum norm. Jet entries are identified by weak derivative equations.
Square integrability is separate from energies, since a divergent Bochner integral
has a default value. These definitions do not depend on quotient or sector interfaces.
-/

noncomputable section

namespace NoEmbeddedEigenvalues

open MeasureTheory Set

/-- Euclidean distance from the chart center. -/
def localRadius (c p : ℝ × ℝ) : ℝ :=
  Real.sqrt ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2)

/-- An open Euclidean disk. -/
def localDisk (c : ℝ × ℝ) (ρ : ℝ) : Set (ℝ × ℝ) := {p | localRadius c p < ρ}

/-- Euclidean disks are open in the product topology. -/
theorem isOpen_localDisk (c : ℝ × ℝ) (r : ℝ) : IsOpen (localDisk c r) := by
  apply isOpen_lt _ continuous_const
  unfold localRadius
  fun_prop

/-- The Euclidean radius is nonzero away from its center. -/
theorem localRadius_ne_zero {c p : ℝ × ℝ} (hp : p ≠ c) : localRadius c p ≠ 0 := by
  intro hz
  have hs : (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 = 0 :=
    (Real.sqrt_eq_zero (by positivity)).mp hz
  have hx : p.1 = c.1 := by nlinarith [sq_nonneg (p.2 - c.2)]
  have hy : p.2 = c.2 := by nlinarith [sq_nonneg (p.1 - c.1)]
  exact hp (Prod.ext hx hy)

/-- Restore a nonnegative integer power of the radius on a bounded disk.
The value at the center does not affect the norm. -/
theorem memLp_of_div_localRadius_pow {c : ℝ × ℝ} {r : ℝ} {s : ℕ} {f : ℝ × ℝ → ℂ}
    (hf : MemLp (fun p ↦ f p / (localRadius c p ^ s : ℂ)) 2
      (volume.restrict (localDisk c r))) : MemLp f 2 (volume.restrict (localDisk c r)) := by
  have hc : Continuous (fun p ↦ (localRadius c p ^ s : ℂ)) := by
    unfold localRadius
    fun_prop
  have hb : MemLp (fun p ↦ (localRadius c p ^ s : ℂ)) ⊤
      (volume.restrict (localDisk c r)) := by
    apply memLp_top_of_bound hc.aestronglyMeasurable (r ^ s)
    filter_upwards [ae_restrict_mem (isOpen_localDisk c r).measurableSet] with p hp
    have hrp : 0 ≤ localRadius c p := Real.sqrt_nonneg _
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrp]
    exact pow_le_pow_left₀ hrp (le_of_lt hp) s
  have hn : ∀ᵐ p ∂(volume.restrict (localDisk c r)), p ≠ c :=
    ae_restrict_of_ae (by
      rw [ae_iff]
      simp [Measure.volume_eq_prod])
  apply (hb.mul hf).ae_eq
  filter_upwards [hn] with p hp
  exact mul_div_cancel₀ _ (pow_ne_zero s (Complex.ofReal_ne_zero.mpr (localRadius_ne_zero hp)))

/-- A uniform comparison between the Euclidean and product-metric radii. -/
theorem localRadius_le_two_dist (c p : ℝ × ℝ) : localRadius c p ≤ 2 * dist p c := by
  have hr : 0 ≤ localRadius c p := Real.sqrt_nonneg _
  have hs : localRadius c p ^ 2 = (p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hx : |p.1 - c.1| ≤ dist p c := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have hy : |p.2 - c.2| ≤ dist p c := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  have hx2 := sq_le_sq₀ (abs_nonneg _) dist_nonneg |>.mpr hx
  have hy2 := sq_le_sq₀ (abs_nonneg _) dist_nonneg |>.mpr hy
  rw [sq_abs] at hx2 hy2
  nlinarith [dist_nonneg (x := p) (y := c)]

/-- A specified weak jet: the head of the word is the outer derivative. -/
def HasWeakJetOn (n : ℕ) (U : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℂ)
    (D : List (Fin 2) → ℝ × ℝ → ℂ) : Prop :=
  D [] = f ∧ ∀ w, w.length < n → ∀ j, HasWeakPartialOn U j (D w) (D (j :: w))

/-- Classical complex jet, with the head of the word as the outer derivative. -/
def classicalComplexJet : List (Fin 2) → (ℝ × ℝ → ℂ) → ℝ × ℝ → ℂ
  | [], f => f
  | j :: w, f => coordPartial j (classicalComplexJet w f)

/-- Square integrability of every order-k derivative divided by the indicated radius power. -/
def RadialJetLp (k s : ℕ) (U : Set (ℝ × ℝ)) (c : ℝ × ℝ)
    (D : List (Fin 2) → ℝ × ℝ → ℂ) : Prop :=
  ∀ w, w.length = k →
    MemLp (fun p ↦ D w p / (localRadius c p ^ s : ℂ)) 2 (volume.restrict U)

/-- The squared radial order-k seminorm; used together with `RadialJetLp`. -/
def radialJetEnergy (k s : ℕ) (U : Set (ℝ × ℝ)) (c : ℝ × ℝ)
    (D : List (Fin 2) → ℝ × ℝ → ℂ) : ℝ :=
  ∑ w : Fin k → Fin 2, ∫ p in U, ‖D (List.ofFn w) p / (localRadius c p ^ s : ℂ)‖ ^ 2

/-- The inhomogeneous squared Sobolev norm of a specified jet. -/
def weakJetEnergy (n : ℕ) (U : Set (ℝ × ℝ))
    (D : List (Fin 2) → ℝ × ℝ → ℂ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), radialJetEnergy k 0 U 0 D

/-- Recursive Sobolev membership and specified square-integrable weak jets agree. -/
theorem memSobolevOn_iff_exists_weakJet {n : ℕ} {U : Set (ℝ × ℝ)}
    {f : ℝ × ℝ → ℂ} :
    MemSobolevOn n U f ↔ ∃ D, HasWeakJetOn n U f D ∧
      ∀ w, w.length ≤ n → MemLp (D w) 2 (volume.restrict U) := by
  induction n generalizing f with
  | zero =>
    constructor
    · intro hf
      let D : List (Fin 2) → ℝ × ℝ → ℂ
        | [] => f
        | _ :: _ => 0
      refine ⟨D, ⟨rfl, fun w hw _ ↦ (Nat.not_lt_zero w.length hw).elim⟩, ?_⟩
      intro w hw
      have he : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
      subst w
      exact hf
    · rintro ⟨D, hD, hL⟩
      change MemLp f 2 (volume.restrict U)
      simpa only [hD.1] using hL [] le_rfl
  | succ n ih =>
    constructor
    · intro hf
      choose g hg hgn using hf.2
      choose E hE hEL using fun j ↦ ih.mp (hgn j)
      -- The last letter selects the first derivative; the remaining word acts on it.
      let D (w : List (Fin 2)) : ℝ × ℝ → ℂ :=
        w.reverseRecOn (motive := fun _ ↦ ℝ × ℝ → ℂ) f (fun v j _ ↦ E j v)
      have hnil : D [] = f := List.reverseRecOn_nil _ _
      have happ (w : List (Fin 2)) (j : Fin 2) : D (w ++ [j]) = E j w :=
        List.reverseRecOn_concat j w _ _
      refine ⟨D, ⟨hnil, ?_⟩, ?_⟩
      · intro w hw i
        cases w using List.reverseRecOn with
        | nil =>
          rw [hnil, show D [i] = g i from (happ [] i).trans (hE i).1]
          exact hg i
        | append_singleton w j =>
          rw [happ, ← List.cons_append, happ]
          exact (hE j).2 w (Nat.lt_of_succ_lt_succ (by simpa using hw)) i
      · intro w hw
        cases w using List.reverseRecOn with
        | nil => simpa only [hnil] using hf.1
        | append_singleton w j =>
          rw [happ]
          exact hEL j w (Nat.le_of_succ_le_succ (by simpa using hw))
    · rintro ⟨D, hD, hL⟩
      refine ⟨by simpa only [hD.1] using hL [] (Nat.zero_le _), fun j ↦ ⟨D [j], ?_, ?_⟩⟩
      · simpa only [hD.1] using hD.2 [] (Nat.zero_lt_succ n) j
      · apply ih.mpr
        refine ⟨fun w ↦ D (w ++ [j]), ⟨rfl, ?_⟩, ?_⟩
        · intro w hw i
          exact hD.2 (w ++ [j]) (by simpa using Nat.succ_lt_succ hw) i
        · intro w hw
          exact hL (w ++ [j]) (by simpa using Nat.succ_le_succ hw)

/-- The coordinate normal to the j-th axis. -/
def axisCoord (j : Fin 2) (p : ℝ × ℝ) : ℝ := if j = 0 then p.1 else p.2

/-- Reflection in the j-th coordinate. -/
def axisReflect (j : Fin 2) (p : ℝ × ℝ) : ℝ × ℝ :=
  if j = 0 then (-p.1, p.2) else (p.1, -p.2)

/-- A rectangle symmetric in the j-th coordinate. -/
def axisRectangle (j : Fin 2) (a l r : ℝ) : Set (ℝ × ℝ) :=
  if j = 0 then Ioo (-a) a ×ˢ Ioo l r else Ioo l r ×ˢ Ioo (-a) a

/-- Real-power radial weights for noninteger cylinder exponents. -/
def RadialJetRpowLp (k : ℕ) (s : ℝ) (U : Set (ℝ × ℝ)) (c : ℝ × ℝ)
    (D : List (Fin 2) → ℝ × ℝ → ℂ) : Prop :=
  ∀ w, w.length = k →
    MemLp (fun p ↦ D w p / (Real.rpow (localRadius c p) s : ℂ)) 2 (volume.restrict U)

end NoEmbeddedEigenvalues
