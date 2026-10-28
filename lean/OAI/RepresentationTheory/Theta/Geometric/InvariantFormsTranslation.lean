import OAI.RepresentationTheory.Theta.Geometric.InvariantAlgebraicForms
import OAI.RepresentationTheory.Theta.Geometric.GroupJetCoordinates
import OAI.RepresentationTheory.Theta.Geometric.CotangentValueExt

/-! # Invariant Forms Translation -/

namespace OAI.RepresentationTheory.Theta.Geometric.InvariantFormsTranslation

noncomputable section

/-! The constructed algebraic cotangent forms are preserved by every
constant left translation of the actual group scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct _root_.CategoryTheory.MonObj

attribute [local instance] Universal.DifferentialJet.differentialOppositeModule

variable {G U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj G] [IsAffine U.left]
    (i : U ⟶ G) [IsOpenImmersion i.left]
    (e : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints U) (he : e ≫ i = 1)
    [Algebra Γ(U.left, ⊤) ℂ] [IsScalarTower ℂ Γ(U.left, ⊤) ℂ]
    (hscalar : ∀ a : Γ(U.left, ⊤), algebraMap Γ(U.left, ⊤) ℂ a = AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e a)

theorem identityCotangentTestValue_leftTranslation (R : CommAlgCat.{0} ℂ)
    (c : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G) (x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G) :
    InvariantAlgebraicForms.identityCotangentTestValue i e he hscalar R (x ≫ GroupJetCoordinates.groupLeftTranslation c) =
      InvariantAlgebraicForms.identityCotangentTestValue i e he hscalar R x := by
  apply CotangentValueExt.pointCotangent_complexLinearMap_ext
  intro a
  rw [InvariantAlgebraicForms.identityCotangentTestValue_D, InvariantAlgebraicForms.identityCotangentTestValue_D,
    GroupJetCoordinates.universalGroupJetCoordinates_leftTranslation]

theorem identityCotangentOneForm_leftTranslation (c : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G)
    (a : InvariantAlgebraicForms.identityChartCotangent U) :
    AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (GroupJetCoordinates.groupLeftTranslation c) (InvariantAlgebraicForms.identityCotangentOneForm i e he hscalar a) =
      InvariantAlgebraicForms.identityCotangentOneForm i e he hscalar a := by
  apply Subtype.ext
  funext R x
  exact LinearMap.congr_fun (identityCotangentTestValue_leftTranslation i e he hscalar R c x) a

end

end OAI.RepresentationTheory.Theta.Geometric.InvariantFormsTranslation
