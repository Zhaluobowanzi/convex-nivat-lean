import Mathlib.Data.Real.Basic
import Nivat.Main
import Nivat.Algebra.ExactLine
import Nivat.Descent.ExactDescent
import Nivat.Dynamics.PeriodicDifference
import Nivat.TwoFactors.Main
import Batteries.Tactic.OpenPrivate

/-! Convex windows. The coordinate-transport and mixed-difference proofs below
adapt the MIT-licensed Nivat/TwoFactors/Main.lean and Nivat/Main.lean in Boon Suan Ho's repository, commit
4e3614024227acd273c3e8ab41df92c2709e5ab0. See LICENSE.upstream. -/
namespace Nivat
open Nivat.Algebra
open private directional_period_of_latticeConvex_mixed_difference periodic_of_directional_period from Nivat.TwoFactors.Main

-- Provenance: PROVENANCE.zh.md#convex_two_factors_nonparallel
/-- A nonparallel mixed difference gives a directional period on a low-complexity convex window. -/
theorem convex_two_factors_nonparallel (c : Configuration ℚ) (hc : FiniteRange c) (W : Finset Lattice)
    (hW : TwoFactors.LatticeConvex W) (h t : Lattice) (hh : h ≠ 0) (_ht : t ≠ 0)
    (hcomplexity : complexity c W ≤ W.card)
    (hmix : difference h (difference t c) = 0)
    (hparallel : h.1 * t.2 ≠ h.2 * t.1) :
    ∃ k : ℤ, k ≠ 0 ∧ (IsPeriod c (k • h) ∨ IsPeriod c (k • t)) := by
  -- Express the original window in a primitive basis for the first direction.
  obtain ⟨q, hq, e, he⟩ := exists_lattice_basis_for_nonzero h hh
  let D := W.map e.symm.toEquiv.toEmbedding
  have hD : ∀ z : Lattice, z ∈ D ↔ e z ∈ W := by
    intro z
    constructor
    · intro hz
      obtain ⟨u, hu, huz⟩ := Finset.mem_map.mp hz
      have heu : e z = u := by rw [← huz]; exact e.apply_symm_apply u
      simpa only [heu] using hu
    · intro hz
      exact Finset.mem_map.mpr ⟨e z, hz, e.symm_apply_apply z⟩
  have hconv : TwoFactors.LatticeConvex D :=
    hW.linear_preimage e (latticeEquivRatLinear e)
      (latticeEquivRatLinear_compatible e) hD
  -- Transport the actual pattern count and mixed difference through that basis.
  have hmap : D.map e.toEquiv.toEmbedding = W := by simp [D, Finset.map_map]
  have hlow : complexity (c ∘ e) D ≤ D.card := by
    change complexity (c ∘ e.toEquiv) D ≤ D.card
    rw [complexity_affine_reindex c e.toEquiv e (map_add e), hmap]
    simpa only [D, Finset.card_map] using hcomplexity
  have hv : (e.symm t).2 ≠ 0 := transverse_coordinate_ne_zero e q he hparallel
  have hmix' : difference ((q : ℤ), 0) (difference (e.symm t) (c ∘ e)) = 0 := by
    change difference ((q : ℤ), 0) (difference (e.symm t) (c ∘ e.toEquiv)) = 0
    rw [difference_affine_reindex c e.toEquiv e (map_add e), e.apply_symm_apply,
      difference_affine_reindex (difference t c) e.toEquiv e (map_add e), he, hmix]
    rfl
  -- Keep the integer multiple while returning to the original coordinates.
  obtain ⟨k, hk, hp⟩ := directional_period_of_latticeConvex_mixed_difference (c ∘ e) (hc.precomp e)
    D hconv hlow q hq (e.symm t) hv hmix'
  refine ⟨k, hk, ?_⟩
  rcases hp with hp | hp
  · left
    simpa only [map_zsmul, he] using
      (isPeriod_affine_reindex_iff c e.toEquiv e (map_add e) _).mp hp
  · right
    simpa only [map_zsmul, e.apply_symm_apply] using
      (isPeriod_affine_reindex_iff c e.toEquiv e (map_add e) _).mp hp

-- Provenance: PROVENANCE.zh.md#convex_two_factors
/-- Convex-window counterpart of Ho’s Theorem 5.1. A finite-range rational configuration with
at most `W.card` patterns on a lattice-convex window and
annihilated by the product of two nonzero directional differences has a
nonzero global period. -/
theorem convex_two_factors (c : Configuration ℚ) (hc : FiniteRange c) (W : Finset Lattice)
    (hW : TwoFactors.LatticeConvex W) (h t : Lattice) (hh : h ≠ 0) (ht : t ≠ 0)
    (hcomplexity : complexity c W ≤ W.card)
    (hmix : difference h (difference t c) = 0) : Periodic c := by
  by_cases hparallel : h.1 * t.2 = h.2 * t.1
  · exact periodic_of_parallel_mixed_difference c hc h t hh ht hparallel hmix
  · exact periodic_of_directional_period c h t hh ht
      (convex_two_factors_nonparallel c hc W hW h t hh ht hcomplexity hmix hparallel)


end Nivat
#print axioms Nivat.convex_two_factors

namespace Nivat
open Nivat.Algebra
open scoped Pointwise

-- Provenance: PROVENANCE.zh.md#line_horizontal
private theorem line_horizontal (e : Lattice ≃+ Lattice) (p : Polynomial ℚ)
    {z : Lattice} (hz : z ∈ (lineEval (e (1,0)) p).coeff.support) :
    (e.symm z).2 = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add] at hz
    rcases Finset.mem_union.mp (Finsupp.support_add hz) with h | h
    · exact hp h
    · exact hq h
  | monomial n r =>
    rw [lineEval_monomial] at hz
    have hs : z = n • e (1,0) := by
      by_contra hn
      apply (Finsupp.mem_support_iff.mp hz)
      exact Finsupp.single_eq_of_ne hn
    rw [hs, map_nsmul, e.symm_apply_apply]
    simp

-- Provenance: PROVENANCE.zh.md#row_endpoint
/-- On each transverse row, the two outermost convolution coefficients survive. -/
private theorem row_endpoint (e : Lattice ≃+ Lattice) (f g : Laurent)
    (horizontal : ∀ a ∈ f.coeff.support, (e.symm a).2 = 0)
    (u : Lattice) (hu : u ∈ f.coeff.support) (z : Lattice) (hz : z ∈ g.coeff.support)
    (s : ℤ) (hs : s = 1 ∨ s = -1) :
    ∃ w ∈ (f*g).coeff.support, (e.symm w).2 = (e.symm (z+u)).2 ∧
        s * (e.symm (z+u)).1 ≤ s * (e.symm w).1 := by
  classical
  let row := g.coeff.support.filter (fun b => (e.symm b).2 = (e.symm z).2)
  have hzr : z ∈ row := Finset.mem_filter.mpr ⟨hz,rfl⟩
  obtain ⟨a,ha,hA⟩ := f.coeff.support.exists_max_image (fun t => s*(e.symm t).1) ⟨u,hu⟩
  obtain ⟨b,hb,hB⟩ := row.exists_max_image (fun t => s*(e.symm t).1) ⟨z,hzr⟩
  obtain ⟨hbg,hby⟩ := Finset.mem_filter.mp hb
  have uniq : UniqueAdd f.coeff.support g.coeff.support a b := by
    intro x y hx hy hxy
    have eqn := congrArg e.symm hxy
    simp only [map_add] at eqn
    have ex := congrArg Prod.fst eqn
    have ey := congrArg Prod.snd eqn
    simp only [Prod.fst_add] at ex
    simp only [Prod.snd_add] at ey
    have ax := horizontal a ha
    have xx := horizontal x hx
    have yr : (e.symm y).2 = (e.symm z).2 := by omega
    have bx := hB y (Finset.mem_filter.mpr ⟨hy,yr⟩)
    have ux := hA x hx
    constructor <;> apply e.symm.injective <;> apply Prod.ext <;>
      rcases hs with rfl | rfl <;> simp only [one_mul, neg_one_mul] at * <;> omega
  refine ⟨a+b, Finsupp.mem_support_iff.mpr ?_, ?_, ?_⟩
  · rw [AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd uniq]
    exact mul_ne_zero (Finsupp.mem_support_iff.mp ha) (Finsupp.mem_support_iff.mp hbg)
  · simp only [map_add, Prod.snd_add, horizontal a ha, horizontal u hu, hby, zero_add, add_zero]
  · have h₁ := hA u hu
    have h₂ := hB z hzr
    simp only [map_add, Prod.fst_add, mul_add]
    linarith

-- Provenance: PROVENANCE.zh.md#convex_line_fit
/-- Support fitting for the line filters that occur in Ho's exact-ideal theorem. -/
theorem convex_line_fit (e : Lattice ≃+ Lattice) (p : Polynomial ℚ)
    (f : Laurent) (hf : f = lineEval (e (1,0)) p) (hne : f ≠ 0) (g : Laurent)
    (D : Finset Lattice) (hc : TwoFactors.LatticeConvex D) :
    (f*g).coeff.support ⊆ D ↔ g.coeff.support ⊆ erodedWindow f hne D := by
  classical
  constructor
  · intro h z hz
    rw [mem_erodedWindow]
    intro u hu
    have hor : ∀ a ∈ f.coeff.support, (e.symm a).2 = 0 := by
      intro a ha
      exact line_horizontal e p (hf ▸ ha)
    obtain ⟨l,hl,hly,hlx⟩ := row_endpoint e f g hor u hu z hz (-1) (Or.inr rfl)
    obtain ⟨r,hr,hry,hrx⟩ := row_endpoint e f g hor u hu z hz 1 (Or.inl rfl)
    let B := D.map e.symm.toEquiv.toEmbedding
    have memB (w : Lattice) : w ∈ B ↔ e w ∈ D := by
      constructor
      · intro hw
        obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hw
        simpa using ha
      · intro hw
        exact Finset.mem_map.mpr ⟨e w, hw, e.symm_apply_apply w⟩
    have hB := hc.linear_preimage e (latticeEquivRatLinear e) (latticeEquivRatLinear_compatible e) memB
    have lift (w : Lattice) (hw : w ∈ D) : e.symm w ∈ B :=
      (memB _).mpr (by simpa using hw)
    have L := lift l (h hl)
    have R := lift r (h hr)
    let t := e.symm (z+u)
    have L' : ((e.symm l).1,t.2) ∈ B := by simpa only [t, ← hly, Prod.mk.eta] using L
    have R' : ((e.symm r).1,t.2) ∈ B := by simpa only [t, ← hry, Prod.mk.eta] using R
    have ht : t ∈ B := hB.row_interval L' R' (by dsimp [t]; omega) (by dsimp [t]; omega)
    simpa [t] using (memB _).mp ht
  · intro h w hw
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset f g hw)
    simpa only [add_comm] using (mem_erodedWindow f hne D b).mp (h hb) a ha

end Nivat

namespace Nivat
open Nivat.Algebra
open private complexity_descent_of_supported_multiples from Nivat.Descent.ExactDescent
open private one_lt_support_card_of_annihilates from Nivat.Algebra.LineErosion

-- Provenance: PROVENANCE.zh.md#convex_erosion
private theorem convex_erosion (f : Laurent) (hf : f ≠ 0)
    (D : Finset Lattice) (hc : TwoFactors.LatticeConvex D) :
    TwoFactors.LatticeConvex (erodedWindow f hf D) := by
  obtain ⟨C,hC,hmem⟩ := hc
  refine ⟨{x | ∀ a ∈ f.coeff.support, x + latticeRatCast a ∈ C}, ?_, ?_⟩
  · intro x hx y hy r s hr hs hrs a ha
    have h := hC (hx a ha) (hy a ha) hr hs hrs
    simpa only [smul_add, add_add_add_comm (r • x), ← add_smul, hrs, one_smul] using h
  · intro z
    rw [mem_erodedWindow]
    simp only [Set.mem_ofPred_eq, hmem]
    have castadd (a : Lattice) : latticeRatCast (z+a) = latticeRatCast z + latticeRatCast a := by
      ext <;> simp [latticeRatCast]
    simp only [castadd]

-- Provenance: PROVENANCE.zh.md#strict_erosion
private theorem strict_erosion (f : Laurent) (hf : f ≠ 0) (D : Finset Lattice)
    (hS : (erodedWindow f hf D).Nonempty)
    (htwo : 1 < f.coeff.support.card) : (erodedWindow f hf D).card < D.card := by
  classical
  let S := erodedWindow f hf D
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
  let T (k : Lattice) := S.image (fun z => z + k)
  have sub (k : Lattice) (hk : k ∈ f.coeff.support) : T k ⊆ D := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    exact (mem_erodedWindow f hf D z).mp hz k hk
  have card (k : Lattice) : (T k).card = S.card :=
    Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)
  by_contra h
  have eqD (k : Lattice) (hk : k ∈ f.coeff.support) : T k = D :=
    Finset.eq_of_subset_of_card_le (sub k hk) (by rw [card]; exact Nat.le_of_not_gt h)
  have sumT (k : Lattice) : (∑ x ∈ T k, x) = (∑ x ∈ S, x) + S.card • k := by
    dsimp [T]
    rw [Finset.sum_image (by intro u _ v _ he; exact add_right_cancel he)]
    simp [Finset.sum_add_distrib]
  have eqsum := (sumT a).symm.trans ((congrArg (fun t : Finset Lattice => ∑ x ∈ t, x)
    ((eqD a ha).trans (eqD b hb).symm)).trans (sumT b))
  have he := add_left_cancel eqsum
  have hcard : 0 < S.card := Finset.card_pos.mpr hS
  apply hab
  apply Prod.ext
  · have hx := congrArg Prod.fst he
    change S.card • a.1 = S.card • b.1 at hx
    simp only [nsmul_eq_mul] at hx
    exact mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt hcard) hx
  · have hy := congrArg Prod.snd he
    change S.card • a.2 = S.card • b.2 at hy
    simp only [nsmul_eq_mul] at hy
    exact mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt hcard) hy

open private line_filter_ne_zero_of_period_divisor from Nivat.Main

-- Provenance: PROVENANCE.zh.md#convex_periodic_of_periodic_line_filter
/-- The polynomial-quotient step in Section 6. If the line-filtered configuration
is periodic, divisibility by `Z^q - 1` gives a mixed-difference identity;
The convex two-factor theorem then gives a period of the original configuration. -/
theorem convex_periodic_of_periodic_line_filter (c : Configuration ℚ) (hc : FiniteRange c)
    (W : Finset Lattice) (hW : TwoFactors.LatticeConvex W)
    (hlow : complexity c W ≤ W.card)
    (v : Lattice) (hv : v ≠ 0) (q : ℕ) (hq : 0 < q)
    (φ : Polynomial ℚ) (hdiv : φ ∣ Polynomial.X ^ q - 1)
    (hfiltered : Periodic (act (lineEval v φ) c)) : Periodic c := by
  obtain ⟨t, ht, hperiod⟩ := hfiltered
  obtain ⟨ψ, hψ⟩ := hdiv
  have hkill : difference t (act (lineEval v φ) c) = 0 :=
    (difference_eq_zero_iff t _).mpr hperiod
  have hmix : difference (q • v) (difference t c) = 0 := by
    rw [difference_comm]
    rw [← act_lineEval_X_pow_sub_one v q c, hψ, map_mul,
      mul_comm (lineEval v φ) (lineEval v ψ), act_mul,
      ← act_difference_comm, hkill, act_config_zero]
  exact convex_two_factors c hc W hW (q • v) t
    (smul_ne_zero (Nat.ne_of_gt hq) hv) ht hlow hmix


-- Provenance: PROVENANCE.zh.md#convex_nivat_rational
/-- Strong induction on the number of lattice sites in the witnessing window. -/
theorem convex_nivat_rational (c : Configuration ℚ) (hc : FiniteRange c)
    (D : Finset Lattice) (hD : TwoFactors.LatticeConvex D)
    (hlow : complexity c D ≤ D.card) : Periodic c := by
  classical
  suffices H : ∀ N : ℕ, ∀ (c : Configuration ℚ), FiniteRange c →
      ∀ D : Finset Lattice, D.card = N → TwoFactors.LatticeConvex D →
      complexity c D ≤ D.card → Periodic c from H _ c hc D rfl hD hlow
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro c hc D hN hD hlow
      by_cases hp : Periodic c
      · exact hp
      obtain ⟨f, hf, hfann⟩ := exists_nonzero_annihilator c hc D hlow
      obtain ⟨x, y, e, q, _hxfin, _hyfin, hx, hy, hd, hq, hperiod, hbelow⟩ :=
        Dynamics.periodic_difference_of_nonzero_annihilator c hc hp f hf hfann
      -- Theorem 4.1 gives the exact line generator required by Corollary 2.3.
      obtain ⟨φ, _hmonic, _hdegree, hdiv, hexact⟩ :=
        exact_line_in_basis e hd hq hperiod hbelow
      have hv : e (1, 0) ≠ 0 := by
        intro hz
        have h := e.injective (hz.trans e.map_zero.symm)
        exact (show ((1, 0) : Lattice) ≠ 0 by decide) h
      let Φ := lineEval (e (1, 0)) φ
      have hΦ : Φ ≠ 0 := line_filter_ne_zero_of_period_divisor (e (1, 0)) hv q hq φ hdiv

      let S := erodedWindow Φ hΦ D
      have hdesc := complexity_descent_of_supported_multiples c hc x y hx hy Φ hΦ D S
        hexact (fun g => convex_line_fit e φ Φ rfl hΦ g D hD)
        (fun z hz => (mem_erodedWindow Φ hΦ D z).mp hz)
      have hlowS : complexity (act Φ c) S ≤ S.card := by omega
      have hfin := finiteRange_act Φ hc
      have hSne := Finset.card_pos.mp ((complexity_pos hfin S).trans_le hlowS)
      have hsmall := strict_erosion Φ hΦ D hSne
        (one_lt_support_card_of_annihilates Φ hΦ (x-y) hd ((hexact Φ).mpr (dvd_refl Φ)))
      have hlt : S.card < N := hN ▸ hsmall
      have hfiltered := ih S.card hlt (act Φ c) hfin S rfl (convex_erosion Φ hΦ D hD) hlowS
      exact convex_periodic_of_periodic_line_filter c hc D hD hlow _ hv q hq φ hdiv hfiltered

-- Provenance: PROVENANCE.zh.md#convex_nivat
/-- Finite-alphabet convex-window Nivat statement, with one nonzero global period. -/
theorem convex_nivat {A : Type*} [Finite A] (c : Configuration A) (D : Finset Lattice)
    (hD : TwoFactors.LatticeConvex D) (hlow : complexity c D ≤ D.card) :
    ∃ h : Lattice, h ≠ 0 ∧ ∀ z : Lattice, c (z+h) = c z := by
  obtain ⟨d, hd, hcomplexity, hperiod⟩ := exists_rational_model c
  obtain ⟨h, hh, hp⟩ := convex_nivat_rational d hd D hD (by rwa [hcomplexity])
  exact ⟨h, hh, (hperiod h).mp hp⟩

end Nivat
#print axioms Nivat.convex_line_fit
#print axioms Nivat.convex_nivat

namespace Nivat

-- Provenance: PROVENANCE.zh.md#convex_two_integer_summands
/-- The integer order-two implication used in the draft. Neither periodic summand
has to take finitely many values. Only their sum has that hypothesis. -/
theorem convex_two_integer_summands (c a b : Configuration ℤ) (hc : FiniteRange c)
    (hsum : c = a + b) (D : Finset Lattice) (hD : TwoFactors.LatticeConvex D)
    (hlow : complexity c D ≤ D.card) (h t : Lattice) (hh : h ≠ 0) (ht : t ≠ 0)
    (ha : IsPeriod a h) (hb : IsPeriod b t) : Periodic c := by
  let i : ℤ → ℚ := fun z => z
  have hi : Function.Injective i := Int.cast_injective
  apply (periodic_map_iff c hi).mp
  apply convex_two_factors (i ∘ c) (hc.map i) D hD h t hh ht
    (by rwa [complexity_map c hi D])
  have haz := (difference_eq_zero_iff h a).mpr ha
  have hbz := (difference_eq_zero_iff t b).mpr hb
  have hv : difference h (difference t c) = 0 := by
    rw [hsum, difference_add, difference_add, difference_comm h t a, haz, hbz]
    funext z
    simp [difference_apply]
  funext z
  have H := congrFun hv z
  simp only [difference_apply, Pi.zero_apply] at H
  change ((c (z+h+t) : ℚ) - c (z+h)) - (c (z+t) - c z) = 0
  exact_mod_cast H

-- Provenance: PROVENANCE.zh.md#convex_nivat_raw
/-- Expanded audit statement with convex hull, translates, pattern count,
and a nonzero global period. Coordinates in the hull are rational. -/
theorem convex_nivat_raw {A : Type*} [Finite A] (c : ℤ × ℤ → A) (D : Finset (ℤ × ℤ))
    (hull : ∀ z : ℤ × ℤ, z ∈ D ↔ ((z.1 : ℚ), (z.2 : ℚ)) ∈
      convexHull ℚ ((fun z : ℤ × ℤ => ((z.1 : ℚ), (z.2 : ℚ))) '' (D : Set (ℤ × ℤ))))
    (low : (Set.range (fun t : ℤ × ℤ => fun z : D => c (z.1+t))).ncard ≤ D.card) :
    ∃ h : ℤ × ℤ, h ≠ (0,0) ∧ ∀ z : ℤ × ℤ, c (z+h) = c z :=
  convex_nivat c D ⟨_, convex_convexHull ℚ _, hull⟩ low

end Nivat
#print axioms Nivat.convex_two_integer_summands
#print axioms Nivat.convex_nivat_raw

-- Provenance: PROVENANCE.zh.md#convex_nivat_real_hull
/-- The geometric form with the ordinary real convex hull, the full lattice,
every translate of the original window, and one nonzero global period. -/
theorem Nivat.convex_nivat_real_hull {A : Type*} [Finite A] (c : ℤ × ℤ → A)
    (D : Finset (ℤ × ℤ))
    (hull : ∀ z : ℤ × ℤ, z ∈ D ↔ ((z.1 : ℝ), (z.2 : ℝ)) ∈
      convexHull ℝ ((fun z : ℤ × ℤ => ((z.1 : ℝ), (z.2 : ℝ))) '' (D : Set (ℤ × ℤ))))
    (low : (Set.range (fun t : ℤ × ℤ => fun z : D => c (z.1+t))).ncard ≤ D.card) :
    ∃ h : ℤ × ℤ, h ≠ (0,0) ∧ ∀ z : ℤ × ℤ, c (z+h) = c z := by
  let C := convexHull ℝ ((fun z : ℤ × ℤ => ((z.1 : ℝ), (z.2 : ℝ))) '' (D : Set (ℤ × ℤ)))
  let castPair (x : ℚ × ℚ) : ℝ × ℝ := (x.1,x.2)
  apply convex_nivat c D _ low
  refine ⟨castPair ⁻¹' C, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    have H := (convex_convexHull ℝ _) (show castPair x ∈ C from hx)
      (show castPair y ∈ C from hy) (show (0 : ℝ) ≤ (a : ℝ) by exact_mod_cast ha)
      (show (0 : ℝ) ≤ (b : ℝ) by exact_mod_cast hb) (by exact_mod_cast hab)
    change castPair (a • x + b • y) ∈ C
    convert H using 1
    ext <;> simp [castPair, smul_eq_mul]
  · intro z
    simpa [castPair, C, latticeRatCast] using hull z

#print axioms Nivat.convex_nivat_real_hull
