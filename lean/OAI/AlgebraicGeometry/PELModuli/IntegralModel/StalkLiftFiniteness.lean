import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.LiftFiniteness
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.GroupTangentsEq
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Stalk Lift Finiteness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.StalkLiftFiniteness

noncomputable section

/-! Relative infinitesimal lifts on a locally finite-type scheme form
a finite module over every noetherian local coefficient ring. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem finite_relative_stalk_lifts {X S : Scheme.{0}} (p : X ⟶ S) [LocallyOfFiniteType p]
    {C : CommRingCat.{0}} [IsLocalRing C] [IsNoetherianRing C]
    (J : Ideal C) (hJ : J ^ 2 = ⊥) (x : X) (e : X.presheaf.stalk x ⟶ C) [IsLocalHom e.hom] :
    Module.Finite C (AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.relativeModule J hJ e p) := by
  let R := S.presheaf.stalk (p x)
  let B := X.presheaf.stalk x
  let : Algebra R B := (p.stalkMap x).hom.toAlgebra
  let : Algebra B C := e.hom.toAlgebra
  let : Algebra R C := (e.hom.comp (p.stalkMap x).hom).toAlgebra
  let : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra.EssFiniteType R B := LocallyOfFiniteType.stalkMap p x
  let q : AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.relativeModule J hJ e p →ₗ[C] Relative.LiftDerivations.RelativeLifts.module R B C J hJ :=
    { toFun := fun v => ⟨v.val, fun r => by
        have h := congrArg (fun f => f.hom r) v.property
        exact h⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let : Module.Finite C (Relative.LiftDerivations.RelativeLifts.module R B C J hJ) := Relative.LiftFiniteness.RelativeLifts.finite R B C J hJ
  apply Module.Finite.of_injective q
  intro v w h
  apply Subtype.ext
  exact congrArg (fun z : Relative.LiftDerivations.RelativeLifts.module R B C J hJ => z.val) h

theorem group_tangent_mem_local_relative
    {S : Scheme.{0}} {C : CommRingCat.{0}} [IsLocalRing C]
    (s : Spec C ⟶ S) (J : Ideal C) (hJ : J ^ 2 = ⊥)
    (A : Over S) [MonObj A] (v : AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.relative s J hJ A) :
    v.val ∈ AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.relativeModule J hJ
      (Scheme.stalkClosedPointTo (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint s A).hom) A.hom := by
  let g : Spec C ⟶ A.left := (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint s A).hom
  let e := Scheme.stalkClosedPointTo g
  let : IsLocalHom (A.hom.stalkMap _ ≫ e).hom :=
    inferInstanceAs (IsLocalHom (e.hom.comp (A.hom.stalkMap _).hom))
  apply AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.toPoint_injective J hJ (A.hom.stalkMap _ ≫ e)
  have he : AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.ofGerm A.left _ e = g := Scheme.Spec_stalkClosedPointTo_fromSpecStalk g
  have ht := AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.toPoint_map J hJ e A.hom v.val
  have hz := AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.toPoint_zero J hJ (A.hom.stalkMap _ ≫ e)
  have hf := AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.ofGerm_comp A.hom _ e
  exact ht.trans ((AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.point_over s J hJ A v).trans
    ((1 : Over.mk s ⟶ A).w.symm.trans
      ((congrArg (fun q => q ≫ A.hom) he).symm.trans (hz.trans hf).symm)))

def groupTangentLocalInclusion
    {S : Scheme.{0}} {C : CommRingCat.{0}} [IsLocalRing C]
    (s : Spec C ⟶ S) (J : Ideal C) (hJ : J ^ 2 = ⊥) (A : Over S) [MonObj A] :
    AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.relative s J hJ A →ₗ[C] AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.relativeModule J hJ
      (Scheme.stalkClosedPointTo (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint s A).hom) A.hom where
  toFun v := ⟨v.val, group_tangent_mem_local_relative s J hJ A v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finite_group_tangent
    {S : Scheme.{0}} {C : CommRingCat.{0}} [IsLocalRing C] [IsNoetherianRing C]
    (s : Spec C ⟶ S) (J : Ideal C) (hJ : J ^ 2 = ⊥)
    (A : Over S) [MonObj A] [LocallyOfFiniteType A.hom] :
    Module.Finite C (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.relative s J hJ A) := by
  let : Module.Finite C (AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.relativeModule J hJ
      (Scheme.stalkClosedPointTo (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint s A).hom) A.hom) :=
    finite_relative_stalk_lifts A.hom J hJ _ _
  apply Module.Finite.of_injective (groupTangentLocalInclusion s J hJ A)
  intro v w h
  apply Subtype.ext
  exact congrArg (fun z : AbelianScheme.TorsionQuotient.LocalLifts.LocalSchemeLifts.relativeModule J hJ
    (Scheme.stalkClosedPointTo (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint s A).hom) A.hom => z.val) h

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.StalkLiftFiniteness
