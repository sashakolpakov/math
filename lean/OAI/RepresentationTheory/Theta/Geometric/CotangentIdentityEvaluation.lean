import OAI.RepresentationTheory.Theta.Geometric.DifferentialJetEvaluation
import OAI.RepresentationTheory.Theta.Geometric.InvariantAlgebraicForms
import OAI.RepresentationTheory.Theta.Geometric.SchemeTangents

/-! # Cotangent Identity Evaluation -/

namespace OAI.RepresentationTheory.Theta.Geometric.CotangentIdentityEvaluation

noncomputable section

/-! At the identity, the constructed algebraic form evaluates on an
actual point derivation by the ordinary cotangent pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct _root_.CategoryTheory.MonObj

attribute [local instance] Universal.DifferentialJet.differentialOppositeModule

variable {R : CommAlgCat.{0} ℂ} (p : R →ₐ[ℂ] ℂ) (δ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations.pointDerivations p)

theorem differentialJetEvaluationMap_native :
    DifferentialJetEvaluation.differentialJetEvaluationMap p δ = SchemeTangents.complexDualNumberIso.inv ≫
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ (Universal.DifferentialJet.differentialJetRing R) (DualNumber ℂ)
        (DifferentialJetEvaluation.differentialJetEvaluation p δ) := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (DifferentialJetEvaluation.differentialJetEvaluation p δ).toRingHom) =
    𝟙 _ ≫ Spec.map (CommRingCat.ofHom (DifferentialJetEvaluation.differentialJetEvaluation p δ).toRingHom)
  rw [Category.id_comp]

theorem pointDerivationSpecJet_native :
    DifferentialJetEvaluation.pointDerivationSpecJet p δ = SchemeTangents.complexDualNumberIso.inv ≫
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (DualNumber ℂ) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations.dualPointOfDerivation p δ).val := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations.dualPointOfDerivation p δ).val.toRingHom) =
    𝟙 _ ≫ Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations.dualPointOfDerivation p δ).val.toRingHom)
  rw [Category.id_comp]

def affineIdentityTest (U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine U.left] :
    AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (CommAlgCat.of ℂ Γ(U.left, ⊤)) ⟶ U :=
  Affine.TestMaps.affineTestMapEquiv U Γ(U.left, ⊤) (AlgHom.id ℂ Γ(U.left, ⊤))

theorem affineIdentityTest_point (U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine U.left]
    (e : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints U) :
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv Γ(U.left, ⊤) (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e) ≫
      affineIdentityTest U = e := by
  change (_ ≫ _) ≫ (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ Γ(U.left, ⊤) Γ(U.left, ⊤)
    (AlgHom.id ℂ Γ(U.left, ⊤)) ≫ (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso U).inv) = _
  have hid : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ Γ(U.left, ⊤) Γ(U.left, ⊤)
      (AlgHom.id ℂ Γ(U.left, ⊤)) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact Spec.map_id _
  rw [hid, Category.id_comp]
  exact (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U).symm_apply_apply e

variable {G U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj G] [IsAffine U.left]
    (i : U ⟶ G) [IsOpenImmersion i.left]
    (e : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints U) (he : e ≫ i = 1)

set_option backward.isDefEq.respectTransparency false in
theorem affineTestMapEquiv_point (f : Γ(U.left, ⊤) →ₐ[ℂ] R) :
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv R p ≫ Affine.TestMaps.affineTestMapEquiv U R f =
      (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U).symm (p.comp f) := by
  change (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexBaseIso.inv ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R ℂ p) ≫
      (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ Γ(U.left, ⊤) R f ≫ (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso U).inv) = _
  rw [Category.assoc, ← Category.assoc (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R ℂ p),
    ← Affine.TestMaps.affineAlgHomOverSpecEquiv_comp]
  rfl

theorem universalGroupJetCoordinates_evaluation_atIdentity
    (f : Γ(U.left, ⊤) →ₐ[ℂ] R) (hp : p.comp f = AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e) :
    (DifferentialJetEvaluation.differentialJetEvaluation p δ).comp
      (GroupJetCoordinates.universalGroupJetCoordinates i e he R (Affine.TestMaps.affineTestMapEquiv U R f ≫ i)) =
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations.dualPointOfDerivation p δ).val.comp f := by
  set_option backward.isDefEq.respectTransparency false in
    let x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G := Affine.TestMaps.affineTestMapEquiv U R f ≫ i
    have hx : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv R p ≫ x = 1 := by
      change AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv R p ≫ (Affine.TestMaps.affineTestMapEquiv U R f ≫ i) = 1
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints U => y ≫ i)
          ((affineTestMapEquiv_point p f).trans
            ((congrArg (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U).symm hp).trans
              ((AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U).symm_apply_apply e)))).trans he)
    have h := DifferentialJetEvaluation.universalGroupJet_evaluation p δ x
    rw [hx, MonObj.comp_one, inv_one, one_mul] at h
    apply (Affine.TestMaps.affineTestMapEquiv U (DualNumber ℂ)).injective
    apply (cancel_epi SchemeTangents.complexDualNumberIso.inv).mp
    apply Over.OverMorphism.ext
    apply (cancel_mono i.left).mp
    change ((SchemeTangents.complexDualNumberIso.inv ≫ Affine.TestMaps.affineTestMapEquiv U (DualNumber ℂ) _) ≫ i).left =
      ((SchemeTangents.complexDualNumberIso.inv ≫ Affine.TestMaps.affineTestMapEquiv U (DualNumber ℂ) _) ≫ i).left
    rw [← Affine.TestMaps.affineTestMapEquiv_comp, ← Category.assoc, ← differentialJetEvaluationMap_native,
      GroupJetCoordinates.universalGroupJetCoordinates_map, Category.assoc, GroupJetCoordinates.universalGroupJetLift_fac, h]
    rw [← Affine.TestMaps.affineTestMapEquiv_comp]
    exact congrArg (fun y : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R =>
      (y ≫ Affine.TestMaps.affineTestMapEquiv U R f ≫ i).left) (pointDerivationSpecJet_native p δ)

variable [Algebra Γ(U.left, ⊤) ℂ] [IsScalarTower ℂ Γ(U.left, ⊤) ℂ]
    (hscalar : ∀ a : Γ(U.left, ⊤), algebraMap Γ(U.left, ⊤) ℂ a = AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e a)

theorem identityCotangentOneForm_atIdentity_D
    (f : Γ(U.left, ⊤) →ₐ[ℂ] R) (hp : p.comp f = AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv U e)
    (a : Γ(U.left, ⊤)) :
    AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection.pointKaehlerValue p δ
      ((InvariantAlgebraicForms.identityCotangentOneForm i e he hscalar
        (1 ⊗ₜ[Γ(U.left, ⊤)] KaehlerDifferential.D ℂ Γ(U.left, ⊤) a)).val
        R (Affine.TestMaps.affineTestMapEquiv U R f ≫ i)) = δ.val (f a) := by
  change AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection.pointKaehlerValue p δ (InvariantAlgebraicForms.identityCotangentTestValue i e he hscalar R _ _) = _
  rw [InvariantAlgebraicForms.identityCotangentTestValue_D]
  exact congrArg TrivSqZeroExt.snd
    (AlgHom.congr_fun (universalGroupJetCoordinates_evaluation_atIdentity p δ i e he f hp) a)

end

end OAI.RepresentationTheory.Theta.Geometric.CotangentIdentityEvaluation
