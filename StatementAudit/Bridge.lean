import StatementAudit.Rectangle
import ConvexNivat
namespace StatementAudit
universe u
open Nivat
-- Provenance: PROVENANCE.zh.md#convex_checked
theorem convex_checked : ConvexStatement.{u} := by
  rintro A _ c D ⟨C,hC,hmem⟩ low
  apply (global_iff c).mp
  apply Nivat.convex_nivat_real_hull c D
  · intro z
    constructor
    · intro hz
      exact subset_convexHull ℝ _ ⟨z,hz,rfl⟩
    · intro hz
      apply (hmem _ _).mpr
      apply convexHull_min _ hC hz
      rintro _ ⟨p,hp,rfl⟩
      exact (hmem _ _).mp hp
  · exact (count_iff_representatives c D _).mpr low

-- Provenance: PROVENANCE.zh.md#order_checked
theorem order_checked : OrderStatement := by
  intro c hc m hm _ hmin D hD low
  let _ : Finite (Set.range c) := hc.to_subtype
  let d (z : ℤ × ℤ) : Set.range c := ⟨c z,z,rfl⟩
  obtain ⟨T,hk,hT⟩ := low
  have reps : RepresentativeOrigins d (fun i j => (i,j) ∈ D) D.card := by
    refine ⟨T,hk,?_⟩
    intro x y
    obtain ⟨t,ht,he⟩ := hT x y
    exact ⟨t,ht,fun i j hij => Subtype.ext (he i j hij)⟩
  obtain ⟨a,b,hn,he⟩ := convex_checked _ d D hD reps
  have period : GlobalPeriod c :=
    ⟨a,b,hn,fun x y => congrArg Subtype.val (he x y)⟩
  have one : HasDecomposition c 1 := ⟨fun _ => c,fun _ => period,fun z => by simp⟩
  have := hmin 1 (by decide) one
  omega

#print axioms StatementAudit.order_checked
#print axioms StatementAudit.convex_checked
end StatementAudit
