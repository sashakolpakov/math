import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CoefficientLieSpace
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.StalkLiftEquivalence

/-! # Coefficient Lie Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CoefficientLieAction.LocalCoefficientLie

noncomputable section

/-! The actual group-scheme action is a coefficient-linear ring action
on local-coefficient relative Lie points. The comparison preserves the
original infinitesimal scheme maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.StalkLiftEquivalence OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

variable {S : Scheme.{0}} {C : Type} [CommRing C] [IsLocalRing C]
  (q : Spec (.of C) ⟶ S)

def groupEquiv (A : Over S) [MonObj A] :
    Relative.InfinitesimalAction.RelativeInfinitesimal.Space (CoefficientLieSpace.LocalCoefficientLie.dualBase C ≫ q) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
      (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) A ≃ₗ[DualNumber C]
        CoefficientLieSpace.LocalCoefficientLie.Space A.hom η[A].left q :=
  PELModuli.IntegralModel.StalkLiftEquivalence.groupTangentLocalEquiv (CoefficientLieSpace.LocalCoefficientLie.dualBase C ≫ q) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
    (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) A

theorem groupEquiv_point (A : Over S) [MonObj A]
    (v : Relative.InfinitesimalAction.RelativeInfinitesimal.Space (CoefficientLieSpace.LocalCoefficientLie.dualBase C ≫ q) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
      (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) A) :
    PELModuli.IntegralModel.Relative.TangentBaseChange.RelativeTangent.point (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C)
        A.hom (CoefficientLieSpace.LocalCoefficientLie.zeroPoint η[A].left q) (groupEquiv q A v) =
      (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.overPoint (CoefficientLieSpace.LocalCoefficientLie.dualBase C ≫ q) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
        (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) A v).left := rfl

variable {R : Type} [CommRing R] {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (ρ : ActionData.IntegralAction R A)

def dualCoefficientAction : R →+* Module.End (DualNumber C) (CoefficientLieSpace.LocalCoefficientLie.Space A.scheme.hom η[A.scheme].left q) :=
  (groupEquiv q A.scheme).conjRingEquiv.toRingHom.comp
    (Relative.InfinitesimalAction.RelativeInfinitesimal.integralAction (CoefficientLieSpace.LocalCoefficientLie.dualBase C ≫ q) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
      (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) A ρ)

def action : R →+* Module.End C (CoefficientLieSpace.LocalCoefficientLie.Space A.scheme.hom η[A.scheme].left q) where
  toFun a := (dualCoefficientAction q A ρ a).restrictScalars C
  map_zero' := by
    rw [map_zero]
    rfl
  map_one' := by
    rw [map_one]
    rfl
  map_add' a b := by
    rw [map_add]
    rfl
  map_mul' a b := by
    rw [map_mul]
    rfl

theorem action_groupEquiv (a : R)
    (v : Relative.InfinitesimalAction.RelativeInfinitesimal.Space (CoefficientLieSpace.LocalCoefficientLie.dualBase C ≫ q) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
      (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) A.scheme) :
    action q A ρ a (groupEquiv q A.scheme v) =
      groupEquiv q A.scheme
        (Relative.InfinitesimalAction.RelativeInfinitesimal.map (CoefficientLieSpace.LocalCoefficientLie.dualBase C ≫ q) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
          (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) (ρ.map a) v) := by
  change groupEquiv q A.scheme
    (Relative.InfinitesimalAction.RelativeInfinitesimal.map (CoefficientLieSpace.LocalCoefficientLie.dualBase C ≫ q) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
      (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) (ρ.map a)
        ((groupEquiv q A.scheme).symm (groupEquiv q A.scheme v))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem action_point (a : R) (v : CoefficientLieSpace.LocalCoefficientLie.Space A.scheme.hom η[A.scheme].left q) :
    PELModuli.IntegralModel.Relative.TangentBaseChange.RelativeTangent.point (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C)
        A.scheme.hom (CoefficientLieSpace.LocalCoefficientLie.zeroPoint η[A.scheme].left q) (action q A ρ a v) =
      PELModuli.IntegralModel.Relative.TangentBaseChange.RelativeTangent.point (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C)
        A.scheme.hom (CoefficientLieSpace.LocalCoefficientLie.zeroPoint η[A.scheme].left q) v ≫ (ρ.map a).left := by
  obtain ⟨w, rfl⟩ := (groupEquiv q A.scheme).surjective v
  rw [action_groupEquiv, groupEquiv_point, groupEquiv_point]
  exact AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point_tangent (CoefficientLieSpace.LocalCoefficientLie.dualBase C ≫ q) (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal C)
    (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.ideal_square C) (ρ.map a) w.val

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CoefficientLieAction.LocalCoefficientLie
