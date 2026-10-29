import NoEmbeddedEigenvalues.SobolevLocal

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
  sorry

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
