import OAI.RepresentationTheory.Theta.Geometric.Affine.PicardUniversality
import OAI.RepresentationTheory.Theta.Geometric.HomogeneousNormalization
import OAI.RepresentationTheory.Theta.Geometric.HomogeneousSheafInjection

/-! # Homogeneous Picard Classes -/

namespace OAI.RepresentationTheory.Theta.Geometric.Affine.HomogeneousPicardClasses

noncomputable section

/-! Every homogeneous line-bundle class on an affine complex test
has the actual parameter in the constructed dual candidate. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem affine_homogeneous_class_has_parameter (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
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
    (q : (AbelianScheme.abelianSchemeOfVariety A).homogeneousPicardPresheaf.obj (.op (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R))) :
    ∃ a : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ N.scheme,
      ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass (AbelianScheme.abelianSchemeOfVariety A) Q.bundle hhomQ a =
        (toSheafify (Scheme.fppfTopology.over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
          (AbelianScheme.abelianSchemeOfVariety A).homogeneousPicardPresheaf).app (.op (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R)) q := by
  let T := AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R
  let L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.toOver).left := q.val.out
  have hLc : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = q.val := Quotient.out_eq _
  let P : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A.toOver T :=
    ⟨AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A.toOver T L, AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_axis A.toOver T L⟩
  have hP : (AbelianScheme.abelianSchemeOfVariety A).IsHomogeneousPicardClass T (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P.bundle) := by
    change (AbelianScheme.abelianSchemeOfVariety A).IsHomogeneousPicardClass T
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A.toOver T L))
    rw [AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_class, hLc]
    exact HomogeneousNormalization.homogeneous_normalizedProductClass (AbelianScheme.abelianSchemeOfVariety A) q.val q.property
  obtain ⟨a, ha, _⟩ := PicardUniversality.existsUnique_affine_picard_parameter A N Q hQ hhomQ hcomplex hH1 P hP
  refine ⟨a, ?_⟩
  apply HomogeneousSheafInjection.homogeneousPicardSheafInclusion_injective (AbelianScheme.abelianSchemeOfVariety A) T
  rw [ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_forget, HomogeneousSheafInjection.homogeneousSheafClass_forget]
  change Q.relativeValue a = (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.toOver).app (.op T) q.val
  apply ha.trans
  change (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.toOver).app (.op T)
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((𝟙 T) ⊗ₘ 𝟙 A.toOver).left (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P.bundle)) = _
  rw [id_tensorHom_id]
  apply (congrArg ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.toOver).app (.op T))
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P.bundle))).trans
  exact (congrArg ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.toOver).app (.op T))
      (AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_class A.toOver T L)).trans
    ((AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass_relative A.toOver T (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).trans
      (congrArg ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.toOver).app (.op T)) hLc))

end

end OAI.RepresentationTheory.Theta.Geometric.Affine.HomogeneousPicardClasses
