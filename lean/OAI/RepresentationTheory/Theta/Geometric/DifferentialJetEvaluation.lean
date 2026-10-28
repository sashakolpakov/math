import OAI.RepresentationTheory.Theta.Geometric.Universal.GroupJet
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection

/-! # Differential Jet Evaluation -/

namespace OAI.RepresentationTheory.Theta.Geometric.DifferentialJetEvaluation

noncomputable section

/-! A point derivation evaluates the universal affine jet in the actual
complex dual numbers. Its infinitesimal component evaluates the actual
Kähler differential. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection
attribute [local instance] Universal.DifferentialJet.differentialOppositeModule

variable {R : CommAlgCat.{0} ℂ} (p : R →ₐ[ℂ] ℂ) (δ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations.pointDerivations p)

def differentialJetEvaluation : Universal.DifferentialJet.differentialJetRing R →ₐ[ℂ] DualNumber ℂ where
  toFun z := (p z.fst, AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection.pointKaehlerValue p δ z.snd)
  map_zero' := by apply TrivSqZeroExt.ext; exact p.map_zero; exact map_zero _
  map_one' := by apply TrivSqZeroExt.ext; exact p.map_one; exact map_zero _
  map_add' z w := by apply TrivSqZeroExt.ext; exact p.map_add _ _; exact map_add _ _ _
  map_mul' z w := by
    apply TrivSqZeroExt.ext
    · exact p.map_mul _ _
    · change AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection.pointKaehlerValue p δ (z.fst • w.snd + w.fst • z.snd) =
        p z.fst * AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection.pointKaehlerValue p δ w.snd + AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection.pointKaehlerValue p δ z.snd * p w.fst
      rw [map_add, AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection.pointKaehlerValue_smul, AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection.pointKaehlerValue_smul, mul_comm (p w.fst)]
  commutes' c := by apply TrivSqZeroExt.ext; exact p.commutes c; exact map_zero _

theorem differentialJetEvaluation_jet :
    (differentialJetEvaluation p δ).comp (Universal.DifferentialJet.differentialJet R) =
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations.dualPointOfDerivation p δ).val := by
  apply AlgHom.ext
  intro r
  apply TrivSqZeroExt.ext
  · rfl
  · exact AlgebraicGeometry.AbelianScheme.TateComparison.KaehlerPointDetection.pointKaehlerValue_D p δ r

theorem differentialJetEvaluation_inl :
    (differentialJetEvaluation p δ).comp
        (TrivSqZeroExt.inlAlgHom ℂ R (KaehlerDifferential ℂ R)) =
      (TrivSqZeroExt.inlAlgHom ℂ ℂ ℂ).comp p := by
  apply AlgHom.ext
  intro r
  apply TrivSqZeroExt.ext
  · rfl
  · exact map_zero _

def differentialJetEvaluationMap : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ Universal.GroupJet.differentialJetTest R :=
  Over.homMk (Spec.map (CommRingCat.ofHom (differentialJetEvaluation p δ).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext (differentialJetEvaluation p δ).commutes)

def pointDerivationSpecJet : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R :=
  Over.homMk (Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations.dualPointOfDerivation p δ).val.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext (AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations.dualPointOfDerivation p δ).val.commutes)

theorem differentialJetEvaluationMap_point :
    differentialJetEvaluationMap p δ ≫ Universal.GroupJet.differentialJetPoint R = pointDerivationSpecJet p δ := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom)) (differentialJetEvaluation_jet p δ)

set_option backward.isDefEq.respectTransparency false in
theorem differentialJetEvaluationMap_projection :
    differentialJetEvaluationMap p δ ≫ Universal.GroupJet.differentialJetProjection R =
      toUnit (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv R p := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv R p).left
  rw [AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv_left, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom)) (differentialJetEvaluation_inl p δ)

set_option backward.isDefEq.respectTransparency false in
theorem universalGroupJet_evaluation {G : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [GrpObj G]
    (x : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest R ⟶ G) :
    differentialJetEvaluationMap p δ ≫ Universal.GroupJet.universalGroupJet R x =
      (toUnit (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ≫ (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv R p ≫ x))⁻¹ *
        (pointDerivationSpecJet p δ ≫ x) := by
  rw [Universal.GroupJet.universalGroupJet, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
    ← Category.assoc, differentialJetEvaluationMap_projection, differentialJetEvaluationMap_point,
    Category.assoc]

end

end OAI.RepresentationTheory.Theta.Geometric.DifferentialJetEvaluation
