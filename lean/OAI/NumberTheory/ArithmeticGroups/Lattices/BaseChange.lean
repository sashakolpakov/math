import OAI.NumberTheory.ArithmeticGroups.Lattices.CoordinateIdeal

/-! # Base Change -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.BaseChange.Construction

noncomputable section

/-! Extension of the concrete matrix-group equations to another field. -/

open scoped Classical
open _root_.MvPolynomial Set

theorem evaluateMatrix_coefficient_map
    {k K L : Type} [Field k] [Field K] [Field L] {n : ℕ}
    (ι : k →+* K) (ρ : K →+* L) (g : Algebraic.SL n L) (p : Algebraic.CoordinatePolynomial n k) :
    Algebraic.evaluateMatrix ρ g (MvPolynomial.map ι p) = Algebraic.evaluateMatrix (ρ.comp ι) g p := by
  exact MvPolynomial.eval₂Hom_map_hom ι _ ρ p

def matrixGroupBaseChange
    {k K : Type} [Field k] [Field K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (ι : k →+* K) : Algebraic.MatrixAlgebraicGroup K n where
  equations := MvPolynomial.map ι '' G.equations
  subgroup L _ ρ := G.subgroup L (ρ.comp ι)
  mem_iff L _ ρ g := by
    rw [G.mem_iff]
    constructor
    · intro h q hq
      obtain ⟨p, hp, rfl⟩ := hq
      rw [evaluateMatrix_coefficient_map]
      exact h p hp
    · intro h p hp
      have he := h (MvPolynomial.map ι p) ⟨p, hp, rfl⟩
      rwa [evaluateMatrix_coefficient_map] at he

theorem coefficient_map_mem_baseChange_vanishingIdeal
    {k K : Type} [Field k] [Field K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (ι : k →+* K)
    {p : Algebraic.CoordinatePolynomial n k} (hp : p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G) :
    MvPolynomial.map ι p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal (matrixGroupBaseChange G ι) := by
  intro L _ ρ x
  rw [evaluateMatrix_coefficient_map]
  exact hp L (ρ.comp ι) x

theorem mem_vanishingIdeal_iff_rational_of_algClosed
    {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (p : Algebraic.CoordinatePolynomial n k) :
    p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G ↔
      ∀ g : G.RationalPoints, Algebraic.evaluateMatrix (RingHom.id k) g.val p = 0 := by
  constructor
  · intro hp g
    exact hp k (RingHom.id k) g
  · intro hp
    rw [CoordinateIdeal.Construction.vanishingIdeal_eq_radical_definingIdeal,
      ← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k)]
    intro x hx
    have hd := hx (CoordinateIdeal.Construction.determinantEquation k n) (Ideal.subset_span (mem_insert _ _))
    have hdet : Matrix.det (fun i j : Fin n => x (i, j)) = 1 := by
      apply sub_eq_zero.mp
      simpa only [MvPolynomial.aeval_eq_eval₂Hom, Algebra.algebraMap_self,
        CoordinateIdeal.Construction.eval_determinantEquation] using hd
    let g : Algebraic.SL n k := ⟨fun i j => x (i, j), hdet⟩
    have hg : g ∈ G.subgroup k (RingHom.id k) := by
      apply (G.mem_iff k (RingHom.id k) g).mpr
      intro q hq
      exact hx q (Ideal.subset_span (mem_insert_of_mem _ hq))
    exact hp ⟨g, hg⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.BaseChange.Construction
