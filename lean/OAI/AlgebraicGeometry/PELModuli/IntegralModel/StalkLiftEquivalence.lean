import OAI.AlgebraicGeometry.PELModuli.IntegralModel.StalkLiftFiniteness
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.LiftDerivations
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

/-! # Stalk Lift Equivalence -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.StalkLiftEquivalence

noncomputable section

/-! Actual relative infinitesimal group points are all relative stalk
derivations, and hence the dual of the base-changed cotangent module. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

theorem groupTangentLocalInclusion_surjective
    {S : Scheme.{0}} {C : CommRingCat.{0}} [IsLocalRing C]
    (s : Spec C ⟶ S) (J : Ideal C) (hJ : J ^ 2 = ⊥) (A : Over S) [MonObj A] :
    Function.Surjective (StalkLiftFiniteness.groupTangentLocalInclusion s J hJ A) := by
  intro v
  have hv : AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point s J hJ A v.val ≫ A.hom = s := by
    have h := AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.toPoint_over J hJ
      (Scheme.stalkClosedPointTo (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint s A).hom) A.hom v
    have he := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint s A).hom
    exact h.trans ((congrArg (fun q => q ≫ A.hom) he).trans (1 : Over.mk s ⟶ A).w)
  have hker : v.val ∈ AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.relative s J hJ A := by
    apply AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point_injective s J hJ (𝟙_ (Over S))
    rw [AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point_tangent, AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point_zero]
    exact hv
  exact ⟨⟨v.val, hker⟩, Subtype.ext rfl⟩

def groupTangentLocalEquiv
    {S : Scheme.{0}} {C : CommRingCat.{0}} [IsLocalRing C]
    (s : Spec C ⟶ S) (J : Ideal C) (hJ : J ^ 2 = ⊥) (A : Over S) [MonObj A] :
    AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.relative s J hJ A ≃ₗ[C] AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.relativeModule J hJ
      (Scheme.stalkClosedPointTo (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint s A).hom) A.hom :=
  LinearEquiv.ofBijective (StalkLiftFiniteness.groupTangentLocalInclusion s J hJ A)
    ⟨by
      intro v w h
      apply Subtype.ext
      exact congrArg (fun z : AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.relativeModule J hJ
        (Scheme.stalkClosedPointTo (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint s A).hom) A.hom => z.val) h,
      groupTangentLocalInclusion_surjective s J hJ A⟩

def localRelativeAlgebraEquiv {X S : Scheme.{0}} (p : X ⟶ S)
    {C : CommRingCat.{0}} [IsLocalRing C] (J : Ideal C) (hJ : J ^ 2 = ⊥)
    (x : X) (e : X.presheaf.stalk x ⟶ C) [IsLocalHom e.hom] :
    letI : Algebra (S.presheaf.stalk (p x)) (X.presheaf.stalk x) := (p.stalkMap x).hom.toAlgebra
    letI : Algebra (X.presheaf.stalk x) C := e.hom.toAlgebra
    letI : Algebra (S.presheaf.stalk (p x)) C := (e.hom.comp (p.stalkMap x).hom).toAlgebra
    letI : IsScalarTower (S.presheaf.stalk (p x)) (X.presheaf.stalk x) C :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.relativeModule J hJ e p ≃ₗ[C]
      Relative.LiftDerivations.RelativeLifts.module (S.presheaf.stalk (p x)) (X.presheaf.stalk x) C J hJ := by
  let : Algebra (S.presheaf.stalk (p x)) (X.presheaf.stalk x) := (p.stalkMap x).hom.toAlgebra
  let : Algebra (X.presheaf.stalk x) C := e.hom.toAlgebra
  let : Algebra (S.presheaf.stalk (p x)) C := (e.hom.comp (p.stalkMap x).hom).toAlgebra
  let : IsScalarTower (S.presheaf.stalk (p x)) (X.presheaf.stalk x) C :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact {
    toFun := fun v => ⟨v.val, fun r => congrArg (fun f => f.hom r) v.property⟩
    invFun := fun v => ⟨v.val, by
      apply AbelianScheme.TorsionQuotient.SquareZero.SquareZeroLifts.Lift.ext
      apply RingHom.ext
      exact v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

def localRelativeCotangentEquiv {X S : Scheme.{0}} (p : X ⟶ S)
    {C : CommRingCat.{0}} [IsLocalRing C] (J : Ideal C) (hJ : J ^ 2 = ⊥)
    (x : X) (e : X.presheaf.stalk x ⟶ C) [IsLocalHom e.hom] :
    letI : Algebra (S.presheaf.stalk (p x)) (X.presheaf.stalk x) := (p.stalkMap x).hom.toAlgebra
    letI : Algebra (X.presheaf.stalk x) C := e.hom.toAlgebra
    AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.relativeModule J hJ e p ≃ₗ[C]
      (C ⊗[X.presheaf.stalk x]
        KaehlerDifferential (S.presheaf.stalk (p x)) (X.presheaf.stalk x) →ₗ[C] J) := by
  let R := S.presheaf.stalk (p x)
  let B := X.presheaf.stalk x
  let : Algebra R B := (p.stalkMap x).hom.toAlgebra
  let : Algebra B C := e.hom.toAlgebra
  let : Algebra R C := (e.hom.comp (p.stalkMap x).hom).toAlgebra
  let : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact (localRelativeAlgebraEquiv p J hJ x e).trans
    ((Relative.LiftDerivations.RelativeLifts.derivationEquiv R B C J hJ).trans (Relative.LiftFiniteness.RelativeLifts.cotangentEquiv R B C J))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.StalkLiftEquivalence
