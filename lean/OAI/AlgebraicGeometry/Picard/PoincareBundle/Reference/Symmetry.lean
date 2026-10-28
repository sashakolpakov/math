import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareInterchange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.DiagonalMultiplicationCompatibility
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PulledMultiplicationUnits
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison

/-! # Symmetry -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.Symmetry.ReferencePoincare

noncomputable section

/-! The original inducing-line formula constructs the normalized symmetry and its two product compatibilities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames

/-- The native diagonal comparison and PoincareBundle's pseudofunctor comparison are the same actual isomorphism. -/
theorem diagonal_comparison {S : Scheme} (A : Over S) (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) :
    AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.diagonalSymmetryComparison A P =
      Pulled.LineBilinear.fiberComparison (β_ A A).hom (Line.Comparison.Bundle.fromShared P)
        (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A) (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A) (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal_swap A) := by
  have h := GlobalPullbackFrame.comparison_eq (β_ A A).hom (Line.Comparison.Bundle.fromShared P)
    (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A) (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A) (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal_swap A)
  simpa only [AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.diagonalSymmetryComparison, Pulled.LineBilinear.fiberComparison,
    Line.Fibers.fiber, NatIso.trans_app, Line.Comparison.Bundle.fromShared] using h.symm

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (ell : A.scheme ⟶ D.abelian.scheme) [IsMonHom ell] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
  (hformula : Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) ell).sheaf (L.pullback (fst A.scheme A.scheme).left).sheaf)
    (L.pullback (snd A.scheme A.scheme).left).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf)) (n : ℕ)

include hformula

omit [IsMonHom ell] in
/-- The symmetry of every multiple follows from the actual source inducing-line formula. -/
theorem existsUnique_symmetry :
    ∃! σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
        (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (ell ^ n)).sheaf ≅
          (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (ell ^ n)).sheaf,
      (Scheme.Modules.pullback (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σ =
        AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.diagonalSymmetryComparison A.scheme (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n)) := by
  have hs := AbelianScheme.IsogenyQuotient.PolarizationLineSymmetry.Construction.lineClass_symmetry_of_polarization_formula A.scheme (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D ell) L hformula
  have hm := AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine_multiple_symmetry D ell n hs
  exact AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.existsUnique_diagonalLineSymmetry_of_iso A.scheme (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n))
    (Classical.choice (Quotient.exact hm))

/-- The unique diagonal-normalized symmetry of the actual multiple Poincare line. -/
def symmetry : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
    (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (ell ^ n)).sheaf ≅
      (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (ell ^ n)).sheaf :=
  Classical.choose (existsUnique_symmetry D ell L hformula n)

omit [IsMonHom ell] in
theorem symmetry_diagonal :
    (Scheme.Modules.pullback (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso (symmetry D ell L hformula n) =
      AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.diagonalSymmetryComparison A.scheme (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n)) :=
  (Classical.choose_spec (existsUnique_symmetry D ell L hformula n)).1

omit hformula L in
/-- The constructed original products have the same source origin unit after scalar pullback. -/
theorem source_units (T : Over (Spec (.of k))) :
    (Pulled.KernelFrames.Poincare.sourceMultiplication (ell ^ n) (Line.Comparison.Bundle.fromShared D.poincare)
      (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D)).unitFrame
        (1 : T ⟶ A.scheme ⊗ A.scheme) (MonObj.one_comp (fst A.scheme A.scheme)) =
    (Poincare.TransverseFrames.sourceVertical (ell ^ n) (Line.Comparison.Bundle.fromShared D.poincare)
      (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D)).unitFrame 1 (MonObj.one_comp (snd A.scheme A.scheme)) :=
  AbelianScheme.IsogenyQuotient.PulledMultiplicationUnits.Construction.sourceMultiplications_unit_zero _ _ _ _ T (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareMultiplications_unit_zero D T)

/-- The constructed normalized symmetry exchanges the full first product with the full second product. -/
theorem symmetry_vertical :
    Symmetric.MultiplicativeFrames.secondMultiplication
      (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (ell ^ n))
      (Pulled.KernelFrames.Poincare.sourceMultiplication (ell ^ n) (Line.Comparison.Bundle.fromShared D.poincare) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D))
      (symmetry D ell L hformula n) =
    Poincare.TransverseFrames.sourceVertical (ell ^ n) (Line.Comparison.Bundle.fromShared D.poincare) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D) := by
  have hn : (Scheme.Modules.pullback (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso (symmetry D ell L hformula n) =
      Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
        (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (ell ^ n)) (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
        (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme) := (symmetry_diagonal D ell L hformula n).trans
          (diagonal_comparison A.scheme (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n)))
  exact AbelianScheme.IsogenyQuotient.DiagonalMultiplicationCompatibility.Construction.secondMultiplication_eq_of_diagonal_normalization A.scheme
    (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (ell ^ n))
    (Pulled.KernelFrames.Poincare.sourceMultiplication (ell ^ n) (Line.Comparison.Bundle.fromShared D.poincare) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D))
    (Poincare.TransverseFrames.sourceVertical (ell ^ n) (Line.Comparison.Bundle.fromShared D.poincare) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D))
    (symmetry D ell L hformula n) hn (source_units D ell n _)

/-- The same actual symmetry gives the reverse product compatibility. -/
theorem symmetry_horizontal :
    Symmetric.TransverseFrames.returnedFirst
      (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (ell ^ n))
      (Poincare.TransverseFrames.sourceVertical (ell ^ n) (Line.Comparison.Bundle.fromShared D.poincare) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D))
      (symmetry D ell L hformula n) =
    Pulled.KernelFrames.Poincare.sourceMultiplication (ell ^ n) (Line.Comparison.Bundle.fromShared D.poincare) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) := by
  have hn : (Scheme.Modules.pullback (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso (symmetry D ell L hformula n) =
      Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
        (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (ell ^ n)) (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A.scheme)
        (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme) := (symmetry_diagonal D ell L hformula n).trans
          (diagonal_comparison A.scheme (AbelianScheme.IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D (ell ^ n)))
  exact AbelianScheme.IsogenyQuotient.DiagonalMultiplicationCompatibility.Construction.returnedFirst_eq_of_diagonal_normalization A.scheme
    (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (ell ^ n))
    (Pulled.KernelFrames.Poincare.sourceMultiplication (ell ^ n) (Line.Comparison.Bundle.fromShared D.poincare) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D))
    (Poincare.TransverseFrames.sourceVertical (ell ^ n) (Line.Comparison.Bundle.fromShared D.poincare) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D))
    (symmetry D ell L hformula n) hn (source_units D ell n _)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.Symmetry.ReferencePoincare
