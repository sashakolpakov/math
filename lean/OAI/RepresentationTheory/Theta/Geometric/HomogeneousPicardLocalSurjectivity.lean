import OAI.RepresentationTheory.Theta.Geometric.Affine.HomogeneousPicardClasses
import OAI.RepresentationTheory.Theta.Geometric.Affine.CoverLocalSurjectivity

/-! # Homogeneous Picard Local Surjectivity -/

namespace OAI.RepresentationTheory.Theta.Geometric.HomogeneousPicardLocalSurjectivity

noncomputable section

/-! The actual homogeneous parameter map is locally surjective for
the fppf topology on every complex test scheme. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem homogeneousParameterMap_locallySurjective (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    [IsProper A.toOver.hom] [Smooth A.toOver.hom] [GeometricallyIntegral A.toOver.hom]
    {n : ℕ} (N : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (Q : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A.toOver N.scheme)
    (hQ : ∀ U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase, Function.Injective (Q.relativeValue (T := U)))
    (hhomQ : (AbelianScheme.abelianSchemeOfVariety A).IsHomogeneousPicardClass N.scheme (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q.bundle))
    (hcomplex : Function.Surjective
      (fun a : Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ N.scheme =>
        ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass (AbelianScheme.abelianSchemeOfVariety A) Q.bundle hhomQ a))
    (hH1 : letI := AlgebraicGeometry.SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) 1
      Module.finrank ℂ (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) 1) ≤ n) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
      (ParameterizedHomogeneousPicard.homogeneousParameterMap (AbelianScheme.abelianSchemeOfVariety A) Q.bundle hhomQ) := by
  let P := (AbelianScheme.abelianSchemeOfVariety A).homogeneousPicardPresheaf
  let G := (AbelianScheme.abelianSchemeOfVariety A).homogeneousPicardSheaf.obj
  let η := toSheafify (Scheme.fppfTopology.over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) P
  apply Affine.CoverLocalSurjectivity.locallySurjective_of_affine_representatives
    (ParameterizedHomogeneousPicard.homogeneousParameterMap (AbelianScheme.abelianSchemeOfVariety A) Q.bundle hhomQ) η
  intro T _ q
  let e := AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso T
  let q' := P.map e.inv.op q
  obtain ⟨a, ha⟩ := Affine.HomogeneousPicardClasses.affine_homogeneous_class_has_parameter A N Q hQ hhomQ hcomplex hH1 q'
  refine ⟨ULift.up (e.hom ≫ a), ?_⟩
  have hq : P.map e.hom.op q' = q := by
    change P.map e.hom.op (P.map e.inv.op q) = q
    rw [← Functor.map_comp_apply, ← op_comp, e.hom_inv_id, op_id, Functor.map_id_apply]
  change ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass (AbelianScheme.abelianSchemeOfVariety A) Q.bundle hhomQ (e.hom ≫ a) =
    η.app (.op T) q
  calc
    _ = G.map e.hom.op (ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass (AbelianScheme.abelianSchemeOfVariety A) Q.bundle hhomQ a) :=
      (ParameterizedHomogeneousPicard.parameterHomogeneousPicardClass_naturality (AbelianScheme.abelianSchemeOfVariety A) Q.bundle hhomQ a e.hom).symm
    _ = G.map e.hom.op (η.app _ q') := congrArg (G.map e.hom.op) ha
    _ = η.app _ (P.map e.hom.op q') := (η.naturality_apply e.hom.op q').symm
    _ = η.app _ q := congrArg (η.app _) hq

end

end OAI.RepresentationTheory.Theta.Geometric.HomogeneousPicardLocalSurjectivity
