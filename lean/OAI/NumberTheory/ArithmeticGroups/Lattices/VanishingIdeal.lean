import OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialAction

/-! # Vanishing Ideal -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.VanishingIdeal.Construction

noncomputable section

/-! The vanishing ideal over all extension fields and its finite generation.
This ideal is stable under translation by points of the matrix group. -/

open scoped Classical
open _root_.MvPolynomial

def coordinateVanishingIdeal {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) : Ideal (Algebraic.CoordinatePolynomial n k) where
  carrier := {p | ∀ (K : Type) [Field K] (ι : k →+* K) (x : G.Points ι),
    Algebraic.evaluateMatrix ι x.val p = 0}
  zero_mem' := by
    intro K _ ι x
    exact map_zero (Algebraic.evaluateMatrix ι x.val)
  add_mem' := by
    intro p q hp hq K _ ι x
    rw [map_add, hp K ι x, hq K ι x, add_zero]
  smul_mem' := by
    intro r p hp K _ ι x
    change Algebraic.evaluateMatrix ι x.val (r * p) = 0
    rw [map_mul, hp K ι x, mul_zero]

theorem equations_subset_vanishingIdeal {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) : G.equations ⊆ coordinateVanishingIdeal G := by
  intro p hp K _ ι x
  exact (G.mem_iff K ι x.val).mp x.property p hp

theorem mem_group_iff_vanishingIdeal {k K : Type} [Field k] [Field K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (ι : k →+* K) (x : Algebraic.SL n K) :
    x ∈ G.subgroup K ι ↔ ∀ p ∈ coordinateVanishingIdeal G, Algebraic.evaluateMatrix ι x p = 0 := by
  constructor
  · exact fun hx p hp => hp K ι ⟨x, hx⟩
  · intro hx
    apply (G.mem_iff K ι x).mpr
    exact fun p hp => hx p (equations_subset_vanishingIdeal G hp)

theorem vanishingIdeal_finitely_generated {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) : (coordinateVanishingIdeal G).FG :=
  IsNoetherian.noetherian _

theorem exists_finite_defining_polynomials {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) :
    ∃ S : Finset (Algebraic.CoordinatePolynomial n k),
      Ideal.span (S : Set (Algebraic.CoordinatePolynomial n k)) = coordinateVanishingIdeal G ∧
      ∀ (K : Type) [Field K] (ι : k →+* K) (x : Algebraic.SL n K),
        x ∈ G.subgroup K ι ↔ ∀ p ∈ S, Algebraic.evaluateMatrix ι x p = 0 := by
  obtain ⟨S, hS⟩ := vanishingIdeal_finitely_generated G
  refine ⟨S, hS, fun K _ ι x => ?_⟩
  rw [mem_group_iff_vanishingIdeal, ← hS]
  constructor
  · exact fun hx p hp => hx p (Ideal.subset_span hp)
  · intro hx p hp
    have hle : Ideal.span (S : Set (Algebraic.CoordinatePolynomial n k)) ≤
        RingHom.ker (Algebraic.evaluateMatrix ι x) := Ideal.span_le.mpr hx
    exact hle hp

theorem rightTranslate_mem_vanishingIdeal {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (g : Algebraic.SL n k) (hg : g ∈ G.subgroup k (RingHom.id k))
    (p : Algebraic.CoordinatePolynomial n k) (hp : p ∈ coordinateVanishingIdeal G) :
    PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k) p ∈ coordinateVanishingIdeal G := by
  intro K _ ι x
  rw [PolynomialAction.Construction.rightTranslate_evaluate]
  have hgK : Matrix.SpecialLinearGroup.map ι g ∈ G.subgroup K ι := by
    have hmap : Matrix.SpecialLinearGroup.map ι g ∈ G.subgroup K (ι.comp (RingHom.id k)) :=
      (G.map (RingHom.id k) ι ⟨g, hg⟩).property
    simpa only [RingHom.comp_id] using hmap
  exact hp K ι ⟨x.val * Matrix.SpecialLinearGroup.map ι g,
    (G.subgroup K ι).mul_mem x.property hgK⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.VanishingIdeal.Construction
