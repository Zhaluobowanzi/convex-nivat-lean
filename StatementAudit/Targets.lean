import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card

namespace StatementAudit
universe u

-- Provenance: PROVENANCE.zh.md#representativeorigins
/-- At most k origins suffice to represent every translated photograph, cell by cell. -/
def RepresentativeOrigins {A : Type u} (c : ℤ × ℤ → A)
    (inside : ℤ → ℤ → Prop) (k : ℕ) : Prop :=
  ∃ T : Finset (ℤ × ℤ), T.card ≤ k ∧ ∀ x y : ℤ, ∃ t ∈ T,
    ∀ i j : ℤ, inside i j → c (x+i,y+j) = c (t.1+i,t.2+j)

-- Provenance: PROVENANCE.zh.md#globalperiod
/-- A single displacement, in signed integer coordinates, works everywhere. -/
def GlobalPeriod {A : Type u} (c : ℤ × ℤ → A) : Prop :=
  ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ x y : ℤ, c (x+a,y+b) = c (x,y)

-- Provenance: PROVENANCE.zh.md#rectanglestatement
def RectangleStatement : Prop :=
  ∀ (A : Type u) [Finite A] (c : ℤ × ℤ → A),
    (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ RepresentativeOrigins c
      (fun i j => 0 ≤ i ∧ i < (m : ℤ) ∧ 0 ≤ j ∧ j < (n : ℤ)) (m*n)) →
    GlobalPeriod c

-- Provenance: PROVENANCE.zh.md#convexstatement
/-- The window is the set of all lattice sites in a convex subset of the real plane. -/
def ConvexStatement : Prop :=
  ∀ (A : Type u) [Finite A] (c : ℤ × ℤ → A) (D : Finset (ℤ × ℤ)),
    (∃ C : Set (ℝ × ℝ), Convex ℝ C ∧ ∀ i j : ℤ, (i,j) ∈ D ↔ ((i : ℝ),(j : ℝ)) ∈ C) →
    RepresentativeOrigins c (fun i j => (i,j) ∈ D) D.card → GlobalPeriod c
-- Provenance: PROVENANCE.zh.md#hasdecomposition
/-- All integer-valued summands are allowed, including those with infinite range. -/
def HasDecomposition (c : ℤ × ℤ → ℤ) (m : ℕ) : Prop :=
  ∃ f : Fin m → (ℤ × ℤ → ℤ), (∀ i, GlobalPeriod (f i)) ∧
    ∀ z, c z = ∑ i, f i z

-- Provenance: PROVENANCE.zh.md#orderstatement
/-- Colle, arXiv:1909.08195v4, Conjecture 1.11. Minimality ranges over all positive lengths. -/
def OrderStatement : Prop :=
  ∀ (c : ℤ × ℤ → ℤ), (Set.range c).Finite → ∀ m : ℕ, 2 ≤ m →
    HasDecomposition c m → (∀ n : ℕ, 0 < n → HasDecomposition c n → m ≤ n) →
    ∀ D : Finset (ℤ × ℤ),
      (∃ C : Set (ℝ × ℝ), Convex ℝ C ∧ ∀ i j : ℤ, (i,j) ∈ D ↔ ((i : ℝ),(j : ℝ)) ∈ C) →
      ¬ RepresentativeOrigins c (fun i j => (i,j) ∈ D) D.card
end StatementAudit
