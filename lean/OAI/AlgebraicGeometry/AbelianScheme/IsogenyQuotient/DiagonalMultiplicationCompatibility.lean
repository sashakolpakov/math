import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationUniqueness
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SymmetricMultiplicationUnits

/-! # Diagonal Multiplication Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DiagonalMultiplicationCompatibility.Construction

noncomputable section

/-! Diagonal normalization of a line symmetry and the common origin
unit determine the full product-exchanging compatibility equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

universe u

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))
  [GrpObj A] [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (L : Picard.PoincareBundle.Line.Bundles.LineBundle (A ⊗ A).left)
  (Dh : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst A A) (snd A A) L) (Dv : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd A A) (fst A A) L)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj L.sheaf ≅ L.sheaf)
  (hnorm : (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal A).left).mapIso σ =
    Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A A).hom L (DiagonalLineSymmetry.Construction.groupDiagonal A) (DiagonalLineSymmetry.Construction.groupDiagonal A)
      (DiagonalLineSymmetry.Construction.groupDiagonal_swap A))
  (hunit : Dh.unitFrame (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A ⊗ A) (MonObj.one_comp (fst A A)) =
    Dv.unitFrame 1 (MonObj.one_comp (snd A A)))

include hnorm in
omit [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] in
theorem diagonalLineSymmetry_at_origin :
    (Scheme.Modules.pullback (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A ⊗ A).left).mapIso σ =
      Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A A).hom L 1 1 (MonObj.one_comp (β_ A A).hom) := by
  have : IsMonHom (DiagonalLineSymmetry.Construction.groupDiagonal A) := by unfold DiagonalLineSymmetry.Construction.groupDiagonal; infer_instance
  exact SymmetricFrameDiagonal.Construction.fixedLineSymmetry_at_point (β_ A A).hom (DiagonalLineSymmetry.Construction.groupDiagonal A) (DiagonalLineSymmetry.Construction.groupDiagonal_swap A) L σ hnorm
    1 1 (MonObj.one_comp (DiagonalLineSymmetry.Construction.groupDiagonal A)) (MonObj.one_comp (β_ A A).hom)

include hnorm hunit in
theorem secondMultiplication_eq_of_diagonal_normalization :
    Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication L Dh σ = Dv := by
  apply MultiplicationUniqueness.Construction.verticalMultiplication_eq_of_origin A A L
  exact (SymmetricMultiplicationUnits.Construction.secondMultiplication_unitFrame_at_fixed_point L σ Dh 1
    (MonObj.one_comp (fst A A)) (MonObj.one_comp (snd A A)) (MonObj.one_comp (β_ A A).hom)
    (diagonalLineSymmetry_at_origin A L σ hnorm)).trans hunit

include hnorm hunit in
theorem returnedFirst_eq_of_diagonal_normalization :
    Picard.PoincareBundle.Symmetric.TransverseFrames.returnedFirst L Dv σ = Dh := by
  apply MultiplicationUniqueness.Construction.horizontalMultiplication_eq_of_origin A A L
  exact (SymmetricMultiplicationUnits.Construction.returnedFirst_unitFrame_at_fixed_point L σ Dv 1
    (MonObj.one_comp (fst A A)) (MonObj.one_comp (snd A A)) (MonObj.one_comp (β_ A A).hom)
    (diagonalLineSymmetry_at_origin A L σ hnorm)).trans hunit.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DiagonalMultiplicationCompatibility.Construction
