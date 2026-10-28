import OAI.RepresentationTheory.Theta.Geometric.Finite.HomogeneousFamilyDescent
import OAI.RepresentationTheory.Theta.Geometric.Picard.FiniteTypeUniversality
import OAI.RepresentationTheory.Theta.Geometric.Picard.ComparisonParameter

/-! # Picard Universality -/

namespace OAI.RepresentationTheory.Theta.Geometric.Affine.PicardUniversality

noncomputable section

/-! The actual complex classification and H1 bound give the unique
Picard parameter over every affine complex test, including non-Noetherian tests. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem existsUnique_affine_picard_parameter (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    [IsProper A.toOver.hom] [Smooth A.toOver.hom] [GeometricallyIntegral A.toOver.hom]
    {n : ℕ} (N : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (Q : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A.toOver N.scheme)
    (hQ : ∀ U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase, Function.Injective (Q.relativeValue (T := U)))
    (hhomQ : (AbelianScheme.abelianSchemeOfVariety A).IsHomogeneousPicardClass N.scheme (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q.bundle))
    (hcomplex : Function.Surjective
      (fun a : Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ N.scheme =>
        ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass (AbelianScheme.abelianSchemeOfVariety A) Q.bundle hhomQ a))
    (hH1 : letI := AlgebraicGeometry.SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) 1
      Module.finrank ℂ (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) 1) ≤ n)
    {R : Type} [CommRing R] [Algebra ℂ R]
    (L : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A.toOver (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R))
    (hL : (AbelianScheme.abelianSchemeOfVariety A).IsHomogeneousPicardClass (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R)
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L.bundle)) :
    ∃! a : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ N.scheme,
      Q.relativeValue a = L.relativeValue (𝟙 (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R)) := by
  obtain ⟨T, hTaff, hTfin, j, M, hM, eM⟩ := Finite.HomogeneousFamilyDescent.exists_finiteType_homogeneous_family A L hL
  let := hTaff
  let := hTfin
  let : IsLocallyNoetherian T.left := LocallyOfFiniteType.isLocallyNoetherian T.hom
  let : LocallyOfFiniteType (N.scheme ⊗ T).hom := by
    change LocallyOfFiniteType (pullback.fst N.scheme.hom T.hom ≫ N.scheme.hom)
    infer_instance
  let : IsLocallyNoetherian (N.scheme ⊗ T).left :=
    LocallyOfFiniteType.isLocallyNoetherian (N.scheme ⊗ T).hom
  let : IsIso (Picard.ParameterComparison.picardParameterProjection Q M).left :=
    Picard.FiniteTypeUniversality.picardParameterProjection_isIso_of_complex_classification A N Q M hQ hhomQ hM hcomplex hH1
  obtain ⟨a, ha⟩ := Picard.ComparisonParameter.exists_picard_parameter_of_comparison_isIso Q M
  have hId : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.line (𝟙 (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R))) =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L.bundle := by
    change AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((𝟙 (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R)) ⊗ₘ 𝟙 A.toOver).left
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L.bundle) = _
    rw [id_tensorHom_id]
    exact AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id _
  have he : M.relativeValue j = L.relativeValue (𝟙 (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R)) := by
    apply congrArg ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.toOver).app (.op (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R)))
    change AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (M.bundle.pullback (j ⊗ₘ 𝟙 A.toOver).left) = _
    rw [tensorHom_id]
    exact (Quotient.sound eM).trans hId.symm
  have hparam : Q.relativeValue (j ≫ a) = L.relativeValue (𝟙 (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R)) := by
    rw [← Q.relativeValue_natural j a, ha, M.relativeValue_natural, Category.comp_id]
    exact he
  exact ⟨j ≫ a, hparam, fun b hb => hQ _ (hb.trans hparam.symm)⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Affine.PicardUniversality
