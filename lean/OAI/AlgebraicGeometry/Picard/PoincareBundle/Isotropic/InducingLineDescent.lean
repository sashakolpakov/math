import OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.TranslationDefectSymmetry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.TranslationSymmetricDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.GroupLineFrame

/-! # Inducing Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.InducingLineDescent

noncomputable section

/-! The actual inducing line descends through an isotropic finite kernel, with the translation defect and its symmetry constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.IntersectionFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
open OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingFormulaSymmetry

attribute [local instance] Kernel.Scheme.kernelGroup Kernel.Scheme.kernelGroup_commutative

variable {k : Type u} [Field k] [IsAlgClosed k] {A B : Over (Spec (.of k))}
  [GrpObj A] [IsCommMonObj A] [GrpObj B]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] [IsIntegral A.left]
  [IsLocallyNoetherian B.left] (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Flat f.left] [Surjective f.left]
  (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left) (L : Line.Bundles.LineBundle A.left)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Kernel.Scheme.kernelObject f ⊗ A).left ≅
    (Scheme.Modules.pullback (Kernel.Scheme.kernelInclusion f ⊗ₘ 𝟙 A).left).obj Q.sheaf)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj Q.sheaf ≅ Q.sheaf)
  (o : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over (Spec (.of k)))).left ≅ Line.Fibers.fiber L η[A])

include e o

/-- Finiteness constructs a kernel-line frame; isotropy proves the cocycle symmetry; splitting and
effective descent then construct the quotient line with an actual pullback isomorphism. -/
theorem exists_descended_line
    (he : (Scheme.Modules.pullback (β_ A A).hom.left).mapIso (InducingFormulaSymmetry.regrouped A Q L e) ≪≫ InducingFormulaSymmetry.targetSymmetry A L =
      InducingFormulaSymmetry.sourceSymmetry A Q L σ ≪≫ InducingFormulaSymmetry.regrouped A Q L e)
    (hi : ∀ (T : Over (Spec (.of k))) (a b : T ⟶ Kernel.Scheme.kernelObject f),
      Kernel.IntersectionFrames.obstruction (Kernel.Scheme.kernelInclusion f) (Kernel.Scheme.kernelInclusion f) (Line.Comparison.Bundle.fromShared Q) s
        (Symmetric.KernelTrivialization.secondFrame (Kernel.Scheme.kernelInclusion f) (Line.Comparison.Bundle.fromShared Q) s σ) a b = 1) :
    ∃ M : Line.Bundles.LineBundle B.left, Nonempty ((Scheme.Modules.pullback f.left).obj M.sheaf ≅ L.sheaf) := by
  have : IsFinite (Kernel.Scheme.kernelObject f).hom := Kernel.Scheme.kernel_isFinite f
  obtain ⟨u⟩ := Finite.GroupLineFrame.exists_frame k (Kernel.Scheme.kernelObject f) (L.pullback (Kernel.Scheme.kernelInclusion f).left)
  apply Kernel.TranslationSymmetricDescent.exists_descended_line f L
    (FramedSubgroupInducingProduct.translationIso (Kernel.Scheme.kernelInclusion f) Q L e s u.symm)
  intro T a b
  exact TranslationDefectSymmetry.value_symmetric (Kernel.Scheme.kernelInclusion f) Q L e s σ u.symm o he hi a b

/-- The inducing formula equivariance is supplied by proper group rigidity, rather than an extra hypothesis. -/
theorem exists_descended_line_of_diagonal
    (hσ : (Scheme.Modules.pullback (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left).mapIso σ = AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.diagonalSymmetryComparison A Q)
    (hi : ∀ (T : Over (Spec (.of k))) (a b : T ⟶ Kernel.Scheme.kernelObject f),
      Kernel.IntersectionFrames.obstruction (Kernel.Scheme.kernelInclusion f) (Kernel.Scheme.kernelInclusion f) (Line.Comparison.Bundle.fromShared Q) s
        (Symmetric.KernelTrivialization.secondFrame (Kernel.Scheme.kernelInclusion f) (Line.Comparison.Bundle.fromShared Q) s σ) a b = 1) :
    ∃ M : Line.Bundles.LineBundle B.left, Nonempty ((Scheme.Modules.pullback f.left).obj M.sheaf ≅ L.sheaf) :=
  exists_descended_line f Q L e s σ o (InducingFormulaFieldSymmetry.formula_equivariant A Q L σ e hσ) hi

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.InducingLineDescent
