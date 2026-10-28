import OAI.NumberTheory.ArithmeticGroups.Lattices.VanishingIdeal

/-! # Coordinate Ideal -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CoordinateIdeal.Construction

noncomputable section

/-! The concrete affine defining ideal, including the determinant-one equation.
Hilbert's Nullstellensatz identifies its radical with the universal vanishing ideal. -/

open scoped Classical
open Set _root_.MvPolynomial

def determinantEquation (k : Type) [Field k] (n : ℕ) : Algebraic.CoordinatePolynomial n k :=
  Matrix.det (fun i j : Fin n => X (i, j)) - 1

theorem eval_determinantEquation {k K : Type} [Field k] [Field K] {n : ℕ}
    (ι : k →+* K) (x : Fin n × Fin n → K) :
    eval₂Hom ι x (determinantEquation k n) = Matrix.det (fun i j => x (i, j)) - 1 := by
  let M : Matrix (Fin n) (Fin n) (Algebraic.CoordinatePolynomial n k) := fun i j => X (i, j)
  have hh := (eval₂Hom ι x).map_det M
  have hmap : (eval₂Hom ι x).mapMatrix M = (fun i j => x (i, j)) := by
    ext i j
    change eval₂Hom ι x (X (i, j)) = x (i, j)
    simp
  rw [hmap] at hh
  change eval₂Hom ι x (M.det - 1) = _
  rw [map_sub, map_one, hh]

def affineDefiningIdeal {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) : Ideal (Algebraic.CoordinatePolynomial n k) :=
  Ideal.span (insert (determinantEquation k n) G.equations)

theorem definingIdeal_le_vanishingIdeal {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) : affineDefiningIdeal G ≤ VanishingIdeal.Construction.coordinateVanishingIdeal G := by
  apply Ideal.span_le.mpr
  intro p hp
  rcases mem_insert_iff.mp hp with rfl | hp
  · intro K _ ι x
    change eval₂Hom ι (fun ij => x.val ij.1 ij.2) (determinantEquation k n) = 0
    rw [eval_determinantEquation]
    have hdet : Matrix.det (x.val : Matrix (Fin n) (Fin n) K) = 1 := x.val.property
    simp only [hdet, sub_self]
  · exact VanishingIdeal.Construction.equations_subset_vanishingIdeal G hp

theorem radical_definingIdeal_le_vanishingIdeal {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) : (affineDefiningIdeal G).radical ≤ VanishingIdeal.Construction.coordinateVanishingIdeal G := by
  intro p hp
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hp
  intro K _ ι x
  have hz := definingIdeal_le_vanishingIdeal G hm K ι x
  rw [map_pow] at hz
  exact eq_zero_of_pow_eq_zero hz

theorem vanishingIdeal_eq_radical_definingIdeal {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) : VanishingIdeal.Construction.coordinateVanishingIdeal G = (affineDefiningIdeal G).radical := by
  apply le_antisymm
  · rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure k)]
    intro p hp x hx
    have hdet0 := hx (determinantEquation k n) (Ideal.subset_span (mem_insert _ _))
    have hdet : Matrix.det (fun i j : Fin n => x (i, j)) = 1 := by
      apply sub_eq_zero.mp
      exact (eval_determinantEquation (algebraMap k (AlgebraicClosure k)) x) ▸ hdet0
    let g : Algebraic.SL n (AlgebraicClosure k) := ⟨fun i j => x (i, j), hdet⟩
    have hg : g ∈ G.subgroup (AlgebraicClosure k) (algebraMap k (AlgebraicClosure k)) := by
      apply (G.mem_iff _ _ _).mpr
      intro q hq
      exact hx q (Ideal.subset_span (mem_insert_of_mem _ hq))
    exact hp (AlgebraicClosure k) (algebraMap k (AlgebraicClosure k)) ⟨g, hg⟩
  · exact radical_definingIdeal_le_vanishingIdeal G

theorem defining_zeroLocus_eq_geometricPoints {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) :
    MvPolynomial.zeroLocus (AlgebraicClosure k) (affineDefiningIdeal G) =
      range (fun g : G.GeometricPoints => fun ij : Fin n × Fin n => g.val ij.1 ij.2) := by
  ext x
  constructor
  · intro hx
    have hdet0 := hx (determinantEquation k n) (Ideal.subset_span (mem_insert _ _))
    have hdet : Matrix.det (fun i j : Fin n => x (i, j)) = 1 := by
      apply sub_eq_zero.mp
      exact (eval_determinantEquation (algebraMap k (AlgebraicClosure k)) x) ▸ hdet0
    let g : Algebraic.SL n (AlgebraicClosure k) := ⟨fun i j => x (i, j), hdet⟩
    have hg : g ∈ G.subgroup (AlgebraicClosure k) (algebraMap k (AlgebraicClosure k)) := by
      apply (G.mem_iff _ _ _).mpr
      exact fun q hq => hx q (Ideal.subset_span (mem_insert_of_mem _ hq))
    exact ⟨⟨g, hg⟩, rfl⟩
  · rintro ⟨g, rfl⟩ p hp
    exact definingIdeal_le_vanishingIdeal G hp (AlgebraicClosure k)
      (algebraMap k (AlgebraicClosure k)) g

theorem mem_vanishingIdeal_iff_geometric {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (p : Algebraic.CoordinatePolynomial n k) :
    p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G ↔
      ∀ x : G.GeometricPoints, Algebraic.evaluateMatrix (algebraMap k (AlgebraicClosure k)) x.val p = 0 := by
  rw [vanishingIdeal_eq_radical_definingIdeal,
    ← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure k),
    defining_zeroLocus_eq_geometricPoints, MvPolynomial.mem_vanishingIdeal_iff]
  simp only [forall_mem_range]
  rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CoordinateIdeal.Construction
