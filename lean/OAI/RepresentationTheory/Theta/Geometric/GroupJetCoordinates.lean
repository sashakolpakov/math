import OAI.RepresentationTheory.Theta.Geometric.Universal.GroupJet
import OAI.RepresentationTheory.Theta.Geometric.Affine.TestMaps

/-! # Group Jet Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric.GroupJetCoordinates

noncomputable section

section

/-! The universal group jet factors through any affine neighborhood of
the identity, with coordinates natural in every affine test algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Universal.DifferentialJet.differentialOppositeModule

variable {G U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj G]
    (i : U ⟶ G) [IsOpenImmersion i.left]
    (e : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints U) (he : e ≫ i = 1)

def universalGroupJetLift (R : CommAlgCat.{0} ℂ) (x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G) :
    Universal.GroupJet.differentialJetTest R ⟶ U :=
  TangentNeighborhoods.tangentNeighborhoodLift (Universal.GroupJet.differentialJetOrigin R) (Universal.GroupJet.differentialJetOrigin_surjective R)
    i (toUnit (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R) ≫ e) (Universal.GroupJet.universalGroupJet R x) (by
      rw [Universal.GroupJet.universalGroupJet_origin, Category.assoc, he, MonObj.comp_one])

theorem universalGroupJetLift_fac (R : CommAlgCat.{0} ℂ) (x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G) :
    universalGroupJetLift i e he R x ≫ i = Universal.GroupJet.universalGroupJet R x :=
  TangentNeighborhoods.tangentNeighborhoodLift_fac _ _ _ _ _ _

theorem universalGroupJetLift_origin (R : CommAlgCat.{0} ℂ) (x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G) :
    Universal.GroupJet.differentialJetOrigin R ≫ universalGroupJetLift i e he R x =
      toUnit (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R) ≫ e :=
  TangentNeighborhoods.tangentNeighborhoodLift_origin _ _ _ _ _ _

theorem universalGroupJetLift_naturality {R S : CommAlgCat.{0} ℂ} (f : R ⟶ S)
    (x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G) :
    Universal.GroupJet.differentialJetSchemeMap f ≫ universalGroupJetLift i e he R x =
      universalGroupJetLift i e he S (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap f ≫ x) := by
  apply Over.OverMorphism.ext
  apply (cancel_mono i.left).mp
  change (Universal.GroupJet.differentialJetSchemeMap f ≫ universalGroupJetLift i e he R x ≫ i).left =
    (universalGroupJetLift i e he S (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap f ≫ x) ≫ i).left
  rw [universalGroupJetLift_fac, universalGroupJetLift_fac, Universal.GroupJet.universalGroupJet_naturality]

variable [IsAffine U.left]

def universalGroupJetCoordinates (R : CommAlgCat.{0} ℂ) (x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G) :
    Γ(U.left, ⊤) →ₐ[ℂ] Universal.DifferentialJet.differentialJetRing R :=
  (Affine.TestMaps.affineTestMapEquiv U (Universal.DifferentialJet.differentialJetRing R)).symm (universalGroupJetLift i e he R x)

theorem universalGroupJetCoordinates_map (R : CommAlgCat.{0} ℂ) (x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G) :
    Affine.TestMaps.affineTestMapEquiv U (Universal.DifferentialJet.differentialJetRing R) (universalGroupJetCoordinates i e he R x) =
      universalGroupJetLift i e he R x := (Affine.TestMaps.affineTestMapEquiv U _).apply_symm_apply _

theorem universalGroupJetCoordinates_fst (R : CommAlgCat.{0} ℂ)
    (x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G) (a : Γ(U.left, ⊤)) :
    (universalGroupJetCoordinates i e he R x a).fst =
      algebraMap ℂ R (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e a) := by
  have h : (TrivSqZeroExt.fstHom ℂ R (KaehlerDifferential ℂ R)).comp
      (universalGroupJetCoordinates i e he R x) =
        (Algebra.ofId ℂ R).comp (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e) := by
    apply (Affine.TestMaps.affineTestMapEquiv U R).injective
    rw [← Affine.TestMaps.affineTestMapEquiv_comp, universalGroupJetCoordinates_map,
      Affine.TestMaps.affineTestMapEquiv_constant, Equiv.symm_apply_apply]
    exact universalGroupJetLift_origin i e he R x
  exact AlgHom.congr_fun h a

theorem universalGroupJetCoordinates_naturality {R S : CommAlgCat.{0} ℂ} (f : R ⟶ S)
    (x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G) :
    (Universal.DifferentialJet.differentialJetMap f).comp (universalGroupJetCoordinates i e he R x) =
      universalGroupJetCoordinates i e he S (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap f ≫ x) := by
  apply (Affine.TestMaps.affineTestMapEquiv U (Universal.DifferentialJet.differentialJetRing S)).injective
  rw [← Affine.TestMaps.affineTestMapEquiv_comp, universalGroupJetCoordinates_map,
    universalGroupJetCoordinates_map]
  exact universalGroupJetLift_naturality i e he f x

end

/-! Constant left translation preserves the actual universal group jet. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Universal.DifferentialJet.differentialOppositeModule

variable {G : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj G]

def groupLeftTranslation (c : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G) : G ⟶ G :=
  (toUnit G ≫ c) * 𝟙 G

theorem groupLeftTranslation_point (c : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G)
    {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (x : T ⟶ G) :
    x ≫ groupLeftTranslation c = (toUnit T ≫ c) * x := by
  rw [groupLeftTranslation, MonObj.comp_mul, ← Category.assoc,
    comp_toUnit, Category.comp_id]

theorem universalGroupJet_leftTranslation (R : CommAlgCat.{0} ℂ)
    (c : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G) (x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G) :
    Universal.GroupJet.universalGroupJet R (x ≫ groupLeftTranslation c) = Universal.GroupJet.universalGroupJet R x := by
  rw [groupLeftTranslation_point, Universal.GroupJet.universalGroupJet, MonObj.comp_mul, MonObj.comp_mul,
    ← Category.assoc, ← Category.assoc, comp_toUnit, comp_toUnit, mul_inv_rev]
  change (Universal.GroupJet.differentialJetProjection R ≫ x)⁻¹ *
      (toUnit (Universal.GroupJet.differentialJetTest R) ≫ c)⁻¹ *
        ((toUnit (Universal.GroupJet.differentialJetTest R) ≫ c) * (Universal.GroupJet.differentialJetPoint R ≫ x)) = _
  rw [mul_assoc, inv_mul_cancel_left]
  rfl

variable {U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine U.left]
    (i : U ⟶ G) [IsOpenImmersion i.left]
    (e : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints U) (he : e ≫ i = 1)

omit [IsAffine U.left] in
theorem universalGroupJetLift_leftTranslation (R : CommAlgCat.{0} ℂ)
    (c : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G) (x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G) :
    universalGroupJetLift i e he R (x ≫ groupLeftTranslation c) =
      universalGroupJetLift i e he R x := by
  apply Over.OverMorphism.ext
  apply (cancel_mono i.left).mp
  change (universalGroupJetLift i e he R (x ≫ groupLeftTranslation c) ≫ i).left =
    (universalGroupJetLift i e he R x ≫ i).left
  rw [universalGroupJetLift_fac, universalGroupJetLift_fac, universalGroupJet_leftTranslation]

theorem universalGroupJetCoordinates_leftTranslation (R : CommAlgCat.{0} ℂ)
    (c : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints G) (x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G) :
    universalGroupJetCoordinates i e he R (x ≫ groupLeftTranslation c) =
      universalGroupJetCoordinates i e he R x := by
  unfold universalGroupJetCoordinates
  rw [universalGroupJetLift_leftTranslation]

end

end OAI.RepresentationTheory.Theta.Geometric.GroupJetCoordinates
