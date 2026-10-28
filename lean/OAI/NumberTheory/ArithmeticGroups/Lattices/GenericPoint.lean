import OAI.NumberTheory.ArithmeticGroups.Lattices.GeometricIrreducibility

/-! # Generic Point -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.GenericPoint.Construction

noncomputable section

/-! A generic matrix point over the fraction field of the coordinate ring. -/

open scoped Classical
open _root_.MvPolynomial

abbrev MatrixCoordinateRing {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) := Algebraic.CoordinatePolynomial n k ⧸ VanishingIdeal.Construction.coordinateVanishingIdeal G

abbrev MatrixFunctionField {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) := FractionRing (MatrixCoordinateRing G)

variable {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
variable [(VanishingIdeal.Construction.coordinateVanishingIdeal G).IsPrime]

def genericCoordinateHom : Algebraic.CoordinatePolynomial n k →+* MatrixFunctionField G :=
  (algebraMap (MatrixCoordinateRing G) (MatrixFunctionField G)).comp
    (Ideal.Quotient.mk (VanishingIdeal.Construction.coordinateVanishingIdeal G))

def genericBaseEmbedding : k →+* MatrixFunctionField G :=
  (genericCoordinateHom G).comp MvPolynomial.C

omit [(VanishingIdeal.Construction.coordinateVanishingIdeal G).IsPrime] in
theorem genericCoordinateHom_eq_eval : genericCoordinateHom G =
    eval₂Hom (genericBaseEmbedding G) (fun ij => genericCoordinateHom G (X ij)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [genericBaseEmbedding]
  · intro ij
    simp

omit [(VanishingIdeal.Construction.coordinateVanishingIdeal G).IsPrime] in
theorem genericCoordinateHom_eq_zero_iff (p : Algebraic.CoordinatePolynomial n k) :
    genericCoordinateHom G p = 0 ↔ p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := by
  change algebraMap (MatrixCoordinateRing G) (MatrixFunctionField G)
      (Ideal.Quotient.mk (VanishingIdeal.Construction.coordinateVanishingIdeal G) p) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective (MatrixCoordinateRing G) (MatrixFunctionField G)),
    Ideal.Quotient.eq_zero_iff_mem]

def genericMatrix : Matrix (Fin n) (Fin n) (MatrixFunctionField G) :=
  fun i j => genericCoordinateHom G (X (i, j))

theorem genericMatrix_det : (genericMatrix G).det = 1 := by
  have hd : CoordinateIdeal.Construction.determinantEquation k n ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G :=
    CoordinateIdeal.Construction.definingIdeal_le_vanishingIdeal G (Ideal.subset_span (Set.mem_insert _ _))
  have hz := (genericCoordinateHom_eq_zero_iff G _).mpr hd
  rw [genericCoordinateHom_eq_eval, CoordinateIdeal.Construction.eval_determinantEquation] at hz
  exact sub_eq_zero.mp hz

def genericSL : Algebraic.SL n (MatrixFunctionField G) := ⟨genericMatrix G, genericMatrix_det G⟩

theorem evaluate_genericSL (p : Algebraic.CoordinatePolynomial n k) :
    Algebraic.evaluateMatrix (genericBaseEmbedding G) (genericSL G) p = genericCoordinateHom G p := by
  change eval₂Hom (genericBaseEmbedding G) (fun ij => genericCoordinateHom G (X ij)) p = _
  rw [← genericCoordinateHom_eq_eval]

theorem genericSL_mem : genericSL G ∈ G.subgroup (MatrixFunctionField G) (genericBaseEmbedding G) := by
  apply (G.mem_iff _ _ _).mpr
  intro p hp
  rw [evaluate_genericSL, genericCoordinateHom_eq_zero_iff]
  exact VanishingIdeal.Construction.equations_subset_vanishingIdeal G hp

def genericPoint : G.Points (genericBaseEmbedding G) := ⟨genericSL G, genericSL_mem G⟩

theorem genericPoint_detects_vanishingIdeal (p : Algebraic.CoordinatePolynomial n k) :
    Algebraic.evaluateMatrix (genericBaseEmbedding G) (genericPoint G).val p = 0 ↔
      p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := by
  rw [show (genericPoint G).val = genericSL G from rfl,
    evaluate_genericSL, genericCoordinateHom_eq_zero_iff]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.GenericPoint.Construction
