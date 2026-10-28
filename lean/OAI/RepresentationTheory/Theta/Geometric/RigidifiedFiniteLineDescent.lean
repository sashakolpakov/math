import OAI.RepresentationTheory.Theta.Geometric.GeneratedLineFiniteDescent
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine

/-! # Rigidified Finite Line Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.RigidifiedFiniteLineDescent

noncomputable section

/-! Finite coefficient descent preserves the actual identity-axis
rigidification, by normalizing the descended line bundle. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem exists_fg_rigidified_abelian_family_line
    {R : Type} [CommRing R] [Algebra ℂ R] (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    [QuasiCompact A.toOver.hom] [QuasiSeparated A.toOver.hom]
    (L : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A.toOver (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R)) :
    ∃ S : Subalgebra ℂ R, S.FG ∧
      ∃ N : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A.toOver (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ S),
        Nonempty ((N.bundle.pullback
          (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val ▷ A.toOver).left).sheaf ≅ L.bundle.sheaf) := by
  obtain ⟨S, hS, N, eN⟩ := GeneratedLineFiniteDescent.exists_fg_abelian_family_line A L.bundle
  let NS : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A.toOver (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ S) :=
    ⟨AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A.toOver (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ S) N,
      AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_axis A.toOver (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ S) N⟩
  refine ⟨S, hS, NS, ?_⟩
  have hN : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf
      (N.pullback (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val ▷ A.toOver).left) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L.bundle := Quotient.sound eN
  have haxis : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      (lift (𝟙 (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R)) (1 : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ A.toOver)).left
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L.bundle) = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R).left :=
    Quotient.sound ⟨L.axis⟩
  suffices h : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (NS.bundle.pullback
      (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val ▷ A.toOver).left) = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L.bundle from
    Quotient.exact h
  change AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val ▷ A.toOver).left
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A.toOver (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ S) N)) = _
  rw [AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_class]
  have hp := AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass_pullback A.toOver
    (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val) (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N)
  have ht : (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val ⊗ₘ 𝟙 A.toOver) =
      (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ S R S.val ▷ A.toOver) := by
    apply hom_ext <;> simp
  rw [ht] at hp
  change AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass _ (AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass _ _ _) =
    AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass A.toOver (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R)
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (N.pullback _)) at hp
  rw [hN, AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass_of_axis A.toOver _ _ haxis] at hp
  exact hp

end

end OAI.RepresentationTheory.Theta.Geometric.RigidifiedFiniteLineDescent
