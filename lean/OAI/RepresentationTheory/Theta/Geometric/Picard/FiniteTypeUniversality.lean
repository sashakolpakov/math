import OAI.RepresentationTheory.Theta.Geometric.Picard.ParameterFlatness
import OAI.RepresentationTheory.Theta.Geometric.OpenRationalPointSurjectivity
import OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard
import OAI.RepresentationTheory.Theta.Geometric.AbelianScheme

/-! # Finite Type Universality -/

namespace OAI.RepresentationTheory.Theta.Geometric.Picard.FiniteTypeUniversality

noncomputable section

/-! Complex-point classification, separation on all tests, and the
algebraic H1 bound give universality for families over every finite-type test. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem picardParameterProjection_isIso_of_complex_classification (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    [IsProper A.toOver.hom] [Smooth A.toOver.hom] [GeometricallyIntegral A.toOver.hom]
    {n : ℕ} (N : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    [LocallyOfFiniteType T.hom] [IsLocallyNoetherian T.left]
    [IsLocallyNoetherian (N.scheme ⊗ T).left]
    (Q : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A.toOver N.scheme) (L : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A.toOver T)
    (hQ : ∀ U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase, Function.Injective (Q.relativeValue (T := U)))
    (hhomQ : (AbelianScheme.abelianSchemeOfVariety A).IsHomogeneousPicardClass N.scheme (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q.bundle))
    (hL : (AbelianScheme.abelianSchemeOfVariety A).IsHomogeneousPicardClass T (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L.bundle))
    (hcomplex : Function.Surjective
      (fun a : Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ N.scheme =>
        ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass (AbelianScheme.abelianSchemeOfVariety A) Q.bundle hhomQ a))
    (hH1 : letI := AlgebraicGeometry.SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) 1
      Module.finrank ℂ (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) 1) ≤ n) :
    IsIso (ParameterComparison.picardParameterProjection Q L).left := by
  have : Flat (ParameterComparison.picardParameterProjection Q L).left :=
    ParameterFlatness.abelian_picardParameterProjection_flat A N Q L hQ hH1
  have : Mono (ParameterComparison.picardParameterProjection Q L) := ParameterComparison.picardParameterProjection_mono Q L hQ
  have : Mono (ParameterComparison.picardParameterProjection Q L).left := Over.mono_left_of_mono _
  apply OpenRationalPointSurjectivity.isIso_of_flat_mono_of_rationalPoints (ParameterComparison.picardParameterProjection Q L)
  intro t
  obtain ⟨a, ha⟩ := hcomplex
    (ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass (AbelianScheme.abelianSchemeOfVariety A) L.bundle hL t)
  have he : Q.relativeValue a = L.relativeValue t :=
    (ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget (AbelianScheme.abelianSchemeOfVariety A) Q.bundle hhomQ a).symm.trans
      ((congrArg ((AbelianScheme.abelianSchemeOfVariety A).homogeneousPicardSheafInclusion.hom.app
        (.op (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))) ha).trans
          (ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget (AbelianScheme.abelianSchemeOfVariety A) L.bundle hL t))
  obtain ⟨z, _, hz⟩ := (ParameterComparison.picardParameterComparison_factorization Q L a t).mp he
  exact ⟨z, hz⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Picard.FiniteTypeUniversality
