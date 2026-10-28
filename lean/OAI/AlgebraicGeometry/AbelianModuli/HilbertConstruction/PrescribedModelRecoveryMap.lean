import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RecoveredIsoLiftCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactoredBaseRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ModelProjectiveEmbedding

/-! # Prescribed Model Recovery Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The original scheme recovers the smooth closed model through an intermediate coefficient base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {C K R : CommRingCat.{u}} (φ : C ⟶ K) (ψ : K ⟶ R)
variable {A : Over (Spec R)} {X : Over (Spec C)}
variable (L : Smooth.ProjectiveClosedModel.SmoothProjectiveClosedModel ((Over.pullback (Spec.map φ)).obj X) (Spec.map ψ))
variable (q : A.left ⟶ X.left) (h : IsPullback q A.hom X.hom (Spec.map ψ ≫ Spec.map φ))

def Smooth.ProjectiveClosedModel.SmoothProjectiveClosedModel.prescribedRecoveryMap : A.left ⟶ L.scheme.left := by
  have : IsIso ((Over.pullback (Spec.map ψ)).map L.embedding) := L.recovered
  exact RecoveredIsoLift.recoveredIsoLift (Spec.map ψ) L.embedding
    (FactoredBaseRecovery.factoredBaseRecovery q A.hom X.hom (Spec.map ψ) (Spec.map φ) h)
    (FactoredBaseRecovery.factoredBaseRecovery_isPullback q A.hom X.hom (Spec.map ψ) (Spec.map φ) h)

theorem Smooth.ProjectiveClosedModel.SmoothProjectiveClosedModel.prescribedRecoveryMap_isPullback :
    IsPullback (L.prescribedRecoveryMap φ ψ q h) A.hom L.scheme.hom (Spec.map ψ) := by
  have : IsIso ((Over.pullback (Spec.map ψ)).map L.embedding) := L.recovered
  exact RecoveredIsoLift.recoveredIsoLift_isPullback _ _ _ _

theorem Smooth.ProjectiveClosedModel.SmoothProjectiveClosedModel.prescribedRecoveryMap_comp_model :
    L.prescribedRecoveryMap φ ψ q h ≫ L.embedding.left =
      FactoredBaseRecovery.factoredBaseRecovery q A.hom X.hom (Spec.map ψ) (Spec.map φ) h := by
  have : IsIso ((Over.pullback (Spec.map ψ)).map L.embedding) := L.recovered
  exact RecoveredIsoLiftCompatibility.recoveredIsoLift_comp _ _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
