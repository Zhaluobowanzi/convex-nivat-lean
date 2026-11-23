import StatementAudit.Targets
import Nivat.Main


namespace StatementAudit
universe u
open Nivat

-- Provenance: PROVENANCE.zh.md#count_iff_representatives
theorem count_iff_representatives {A : Type*} [Finite A] (c : ℤ × ℤ → A)
    (D : Finset (ℤ × ℤ)) (k : ℕ) :
    complexity c D ≤ k ↔ RepresentativeOrigins c (fun i j => (i,j) ∈ D) k := by
  classical
  let f := patternAt c D
  let P := Set.range f
  have hP : P.Finite := patterns_finite (finiteRange_of_finite c) D
  let _ : Fintype P := hP.fintype
  let origin (p : P) := Classical.choose p.property
  have atOrigin (p : P) : f (origin p) = p.val := Classical.choose_spec p.property
  have cells (x t : ℤ × ℤ) : f x = f t ↔
      ∀ i j : ℤ, (i,j) ∈ D → c (x.1+i,x.2+j) = c (t.1+i,t.2+j) := by
    obtain ⟨x₁,x₂⟩ := x
    obtain ⟨t₁,t₂⟩ := t
    constructor
    · intro h i j hz
      simpa only [f, patternAt, Prod.mk_add_mk, add_comm] using congrFun h ⟨(i,j),hz⟩
    · intro h
      funext ⟨⟨i,j⟩, hz⟩
      simpa only [f, patternAt, Prod.mk_add_mk, add_comm] using h i j hz
  constructor
  · intro h
    refine ⟨Finset.univ.image origin, Finset.card_image_le.trans ?_, ?_⟩
    · change P.ncard ≤ k at h
      simpa only [Finset.card_univ, Set.ncard_eq_toFinset_card', Set.toFinset_card] using h
    · intro x y
      let p : P := ⟨f (x,y), ⟨(x,y),rfl⟩⟩
      exact ⟨origin p, Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩,
        (cells _ _).mp (atOrigin p).symm⟩
  · rintro ⟨T,hk,hT⟩
    have sub : P ⊆ f '' (T : Set (ℤ × ℤ)) := by
      rintro _ ⟨⟨x,y⟩,rfl⟩
      obtain ⟨t,ht,he⟩ := hT x y
      exact ⟨t,ht,((cells _ _).mpr he).symm⟩
    change P.ncard ≤ k
    exact (Set.ncard_le_ncard sub (T.finite_toSet.image f)).trans
      ((Set.ncard_image_le T.finite_toSet).trans (by simpa using hk))

-- Provenance: PROVENANCE.zh.md#global_iff
theorem global_iff {A : Type*} (c : ℤ × ℤ → A) : Periodic c ↔ GlobalPeriod c := by
  constructor
  · rintro ⟨⟨a,b⟩,hn,h⟩
    exact ⟨a,b,by by_contra! he; exact hn (Prod.ext he.1 he.2),fun x y => h (x,y)⟩
  · rintro ⟨a,b,hn,h⟩
    exact ⟨(a,b),by rintro he; rcases hn with ha|hb; exact ha (congrArg Prod.fst he); exact hb (congrArg Prod.snd he),fun z => h z.1 z.2⟩

-- Provenance: PROVENANCE.zh.md#rectangle_checked
theorem rectangle_checked : RectangleStatement.{u} := by
  rintro A _ c ⟨m,n,hm,hn,low⟩
  apply (global_iff c).mp
  apply Nivat.nivat c m n hm hn
  apply (count_iff_representatives c _ _).mpr
  simpa only [mem_rectangle, Prod.mk.injEq] using low

#print axioms StatementAudit.count_iff_representatives
#print axioms StatementAudit.global_iff
#print axioms StatementAudit.rectangle_checked
end StatementAudit
