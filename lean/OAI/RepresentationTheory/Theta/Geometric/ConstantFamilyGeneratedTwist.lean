import OAI.RepresentationTheory.Theta.Geometric.ConstantFamilyProjectiveEmbedding
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ClosedGlobalGeneration
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ScalarBundle
import OAI.AlgebraicGeometry.SheafCohomology.Projective.UniversalPowers
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree

/-! # Constant Family Generated Twist -/

namespace OAI.RepresentationTheory.Theta.Geometric.ConstantFamilyGeneratedTwist

noncomputable section

/-! Every line bundle on an arbitrary affine parameter family becomes
globally generated after a twist pulled back from the original variety. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open OAI.AlgebraicGeometry.SheafCohomology.Projective.ScalarBundle

attribute [local instance] MvPolynomial.gradedAlgebra AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

variable (A : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) {n : ℕ}
    (e : A.left ⟶ Projective.Map.RelativeProjective.projectiveSpace ℂ n)
    (he : e ≫ Projective.Map.RelativeProjective.projectiveSpaceToBase ℂ n = A.hom)
    (R : Type) [CommRing R] [Algebra ℂ R]

def constantFamilyHyperplaneIso :
    (Scheme.Modules.pullback (ConstantFamilyProjectiveEmbedding.constantFamilyProjectiveEmbedding A e he R)).obj
      (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := R) (0 : Fin (n + 1))).sheaf ≅
    (((AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := ℂ) (0 : Fin (n + 1))).pullback e).pullback
      (snd (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R) A).left).sheaf := by
  let f := ConstantFamilyProjectiveEmbedding.constantFamilyProjectiveEmbedding A e he R
  let p := (snd (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R) A).left
  let c := AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveI.Scalars.map (algebraMap ℂ R) n
  have hc : f ≫ c = p ≫ e := ConstantFamilyProjectiveEmbedding.constantFamilyProjectiveEmbedding_coefficient A e he R
  exact (Scheme.Modules.pullback f).mapIso
      (AlgebraicGeometry.SheafCohomology.Projective.ScalarBundle.projectiveScalarMap_bundleIso (algebraMap ℂ R) n 0 0).symm ≪≫
    (Scheme.Modules.pullbackComp f c).app _ ≪≫
    (Scheme.Modules.pullbackCongr hc).app _ ≪≫
    (Scheme.Modules.pullbackComp p e).symm.app _

include he in
theorem exists_constant_family_generated_twist [IsClosedImmersion e]
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⊗ A).left) :
    ∃ H : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left,
      AlgebraicGeometry.SheafCohomology.Projective.FiniteGlobalGenerators.HasFiniteGlobalGenerators (L.tensor (H.pullback (snd (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R) A).left)).sheaf := by
  let f := ConstantFamilyProjectiveEmbedding.constantFamilyProjectiveEmbedding A e he R
  let p := (snd (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R) A).left
  let H := (AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveCoordinatesApp.Construction.ProjectiveCoordinates.bundle (R := ℂ) (0 : Fin (n + 1))).pullback e
  let : L.sheaf.IsQuasicoherent := AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  let : L.sheaf.IsFinitePresentation := AlgebraicGeometry.Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation L
  obtain ⟨k, hk⟩ := AlgebraicGeometry.SheafCohomology.Projective.ClosedGlobalGeneration.Dimension.closedProjective_eventually_hasFiniteGlobalGenerators f L.sheaf 0
  let eTw := AlgebraicGeometry.SheafCohomology.Projective.UniversalPowers.Dimension.pullbackProjectiveTwistUniversalIso f 0 (H.pullback p)
    (constantFamilyHyperplaneIso A e he R) k ≪≫
      (AlgebraicGeometry.Quotients.FiniteDescent.TensorPullback.Construction.TensorPullbackMap.iso p H k).symm
  refine ⟨H.tensorPower k, (hk k le_rfl).of_iso ?_⟩
  exact whiskerLeftIso L.sheaf eTw ≪≫ AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalTensorObjIso _ _

end

end OAI.RepresentationTheory.Theta.Geometric.ConstantFamilyGeneratedTwist
