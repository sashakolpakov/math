import OAI.RepresentationTheory.Theta.Geometric.SquareZero.ParameterReflection
import OAI.RepresentationTheory.Theta.Geometric.SquareZero.PicardInjectivity

/-! # Parameter Separation -/

namespace OAI.RepresentationTheory.Theta.Geometric.SquareZero.ParameterSeparation

noncomputable section

/-! Dual-number separation also detects square-zero parameters after
their inclusion into an arbitrary ambient complex algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem parameterPicardClass_squareZero_composite_injective
    {V R S : Type} [AddCommGroup V] [Module ℂ V] [Module ℂᵐᵒᵖ V] [IsCentralScalar ℂ V]
    [CommRing R] [Algebra ℂ R] [Nontrivial R] [CommRing S] [Algebra ℂ S] [Nontrivial S]
    (i : V →ₗ[ℂ] R) (hi : Function.Injective i) (hsq : ∀ x y, i x * i y = 0)
    (q : R →ₐ[ℂ] S) (he : Function.Exact i q.toLinearMap)
    {n : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) {P : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)
    (eQ : (Q.pullback (lift (𝟙 P) (1 : P ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule P.left)
    (hinj : Function.Injective (fun t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ P => ParameterizedPicardClass.parameterPicardClass Q t)) :
    Function.Injective (fun t : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (TrivSqZeroExt ℂ V) ⟶ P =>
      ParameterizedPicardClass.parameterPicardClass Q (Normalized.SquareZeroDescent.complexSquareZeroParameterMap i hsq ≫ t)) := by
  intro a b hab
  apply PicardInjectivity.parameterPicardClass_squareZero_injective Q hinj V
  exact ParameterReflection.parameterPicardClass_squareZero_reflects i hi hsq q he A Q eQ a b hab

end

end OAI.RepresentationTheory.Theta.Geometric.SquareZero.ParameterSeparation
