import OAI.NumberTheory.ArithmeticGroups.Lattices.ExteriorCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.Realizations

/-! # Polynomial Continuity -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialContinuity.Construction

noncomputable section

/-! Continuity of finite polynomial and exterior representations follows
from their polynomial matrix coefficients. -/

open scoped Classical

theorem continuous_polynomialMatrixCoefficient
    {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ}
    (φ : Algebraic.CoordinatePolynomial n k →ₗ[k] k) (p : Algebraic.CoordinatePolynomial n k) :
    Continuous (fun g : Algebraic.SL n k => φ (PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k) p)) := by
  have he (g : Algebraic.SL n k) :
      Algebraic.evaluateMatrix (RingHom.id k) g (UniversalRightTranslation.Construction.polynomialMatrixCoefficient φ p) =
        φ (PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k) p) := by
    rw [UniversalRightTranslation.Construction.evaluate_polynomialMatrixCoefficient]
    simpa only [MvPolynomial.map_id, RingHom.id_apply] using
      PolynomialFunctionalExtension.Construction.polynomialFunctionalMap_coefficient_map (RingHom.id k) φ
        (PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k) p)
  simp_rw [← he]
  exact Algebraic.MatrixAlgebraicGroup.continuous_evaluateMatrix (RingHom.id k) _

theorem continuous_boundedPolynomial_functional
    {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n d : ℕ}
    (φ : BoundedRepresentation.Construction.BoundedPolynomials k n d →ₗ[k] k) (p : BoundedRepresentation.Construction.BoundedPolynomials k n d) :
    Continuous (fun g : Algebraic.SL n k => φ (BoundedRepresentation.Construction.boundedPolynomialRepresentation d g p)) := by
  obtain ⟨ψ, hψ⟩ := φ.exists_extend
  have he (g : Algebraic.SL n k) : φ (BoundedRepresentation.Construction.boundedPolynomialRepresentation d g p) =
      ψ (PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k) p.val) :=
    (LinearMap.congr_fun hψ (BoundedRepresentation.Construction.boundedPolynomialRepresentation d g p)).symm
  simp_rw [he]
  exact continuous_polynomialMatrixCoefficient ψ p.val

theorem continuous_boundedExterior_basis_coordinate
    {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n d r : ℕ}
    (s t : ExteriorCoordinates.Construction.BoundedExteriorIndices n d r) :
    Continuous (fun g : Algebraic.SL n k => ExteriorCoordinates.Construction.boundedExteriorCoordinates k n d r
      (ExteriorRepresentation.Construction.boundedExteriorRepresentation d r g (ExteriorCoordinates.Construction.boundedExteriorBasis k n d r t)) s) := by
  have he (g : Algebraic.SL n k) : ExteriorCoordinates.Construction.boundedExteriorCoordinates k n d r
      (ExteriorRepresentation.Construction.boundedExteriorRepresentation d r g (ExteriorCoordinates.Construction.boundedExteriorBasis k n d r t)) s =
      (Matrix.of (fun i j => (BoundedMonomialBasis.Construction.boundedMonomialBasis k n d).coord
        (Set.powersetCard.ofFinEmbEquiv.symm s j)
          (BoundedRepresentation.Construction.boundedPolynomialRepresentation d g
            (BoundedMonomialBasis.Construction.boundedMonomialBasis k n d (Set.powersetCard.ofFinEmbEquiv.symm t i))))).det := by
    change ExteriorCoordinates.Construction.boundedExteriorCoordinates k n d r
      (exteriorPower.map r (BoundedRepresentation.Construction.boundedPolynomialRepresentation d g).toLinearMap
        ((BoundedMonomialBasis.Construction.boundedMonomialBasis k n d).exteriorPower r t)) s = _
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.map_apply_ιMulti,
      ExteriorCoordinates.Construction.boundedExteriorCoordinates_wedge]
    rfl
  simp_rw [he]
  have hm : Continuous (fun g : Algebraic.SL n k => Matrix.of (fun i j =>
      (BoundedMonomialBasis.Construction.boundedMonomialBasis k n d).coord (Set.powersetCard.ofFinEmbEquiv.symm s j)
        (BoundedRepresentation.Construction.boundedPolynomialRepresentation d g
          (BoundedMonomialBasis.Construction.boundedMonomialBasis k n d (Set.powersetCard.ofFinEmbEquiv.symm t i))))) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuous_boundedPolynomial_functional (k := k)
      ((BoundedMonomialBasis.Construction.boundedMonomialBasis k n d).coord (Set.powersetCard.ofFinEmbEquiv.symm s j))
      (BoundedMonomialBasis.Construction.boundedMonomialBasis k n d (Set.powersetCard.ofFinEmbEquiv.symm t i))
  exact hm.matrix_det

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialContinuity.Construction
