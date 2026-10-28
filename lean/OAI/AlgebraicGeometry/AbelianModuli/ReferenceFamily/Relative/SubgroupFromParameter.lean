import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ParameterPointTransport

/-! # Subgroup From Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.SubgroupFromParameter

noncomputable section

/-! Recover a relative subgroup of the original group from a subgroup
over the parameter scheme. This is inverse to the ordinary passage
to that parameter, with exact all-test membership and kernel type. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

universe u

def terminalParameterPoint {S : Scheme.{u}} (X : Over S) :
    X ⟶ Over.mk (𝟙 S) := Over.homMk X.hom (Category.comp_id _)

theorem terminalParameterPoint_unique {S : Scheme.{u}} (X : Over S)
    (t : X ⟶ Over.mk (𝟙 S)) : terminalParameterPoint X = t := by
  apply Over.OverMorphism.ext
  exact ((Category.comp_id t.left).symm.trans t.w).symm

variable {S : Scheme.{u}} (G : Grp (Over S)) (P : Over S)

def relativeSubgroupFromParameter
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup ((Over.pullback P.hom).obj G.X) (Over.mk (𝟙 P.left))) :
    AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P where
  points X t := (F.points (Over.mk t.left) (terminalParameterPoint (Over.mk t.left))).comap
    (ParameterPointTransport.parameterPointMulEquiv G P X t).toMonoidHom
  naturality := by
    intro X Y a t x hx
    have h := F.naturality (ParameterPointTransport.parameterTestMap P a t) (terminalParameterPoint (Over.mk t.left)) hx
    rw [← terminalParameterPoint_unique _
      (ParameterPointTransport.parameterTestMap P a t ≫ terminalParameterPoint (Over.mk t.left))] at h
    change ParameterPointTransport.parameterPointMulEquiv G P X (a ≫ t) (a ≫ x) ∈
      F.points (Over.mk (a ≫ t).left) (terminalParameterPoint (Over.mk (a ≫ t).left))
    rw [ParameterPointTransport.parameterPointMulEquiv_natural]
    exact h

theorem relativeSubgroupFromParameter_overParameter
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup ((Over.pullback P.hom).obj G.X) (Over.mk (𝟙 P.left))) :
    AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P (relativeSubgroupFromParameter G P F) = F := by
  ext X t x
  change ParameterPointTransport.parameterPointMulEquiv G P ((Over.map P.hom).obj X) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P X)
      ((AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G X).symm x) ∈
        F.points X (terminalParameterPoint X) ↔ x ∈ F.points X t
  rw [ParameterPointTransport.parameterPointMulEquiv_canonical, MulEquiv.apply_symm_apply, terminalParameterPoint_unique X t]

theorem relativeSubgroup_membership_iso {A X Y Q : Over S} [GrpObj A]
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A Q) (e : X ≅ Y) (t : Y ⟶ Q) (x : Y ⟶ A) :
    e.hom ≫ x ∈ F.points X (e.hom ≫ t) ↔ x ∈ F.points Y t := by
  constructor
  · intro hx
    have h := F.naturality e.inv (e.hom ≫ t) hx
    simpa only [← Category.assoc, e.inv_hom_id, Category.id_comp] using h
  · exact F.naturality e.hom t

theorem relativeSubgroupOverParameter_fromParameter (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P) :
    relativeSubgroupFromParameter G P (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F) = F := by
  ext X t x
  let e := ParameterPointTransport.parameterTestIso P X t
  have ht : AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P (Over.mk t.left) = e.hom ≫ t := by
    apply Over.OverMorphism.ext
    exact (Category.id_comp t.left).symm
  change (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (Over.mk t.left)).symm
      (ParameterPointTransport.parameterPointMulEquiv G P X t x) ∈
        F.points ((Over.map P.hom).obj (Over.mk t.left)) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P (Over.mk t.left)) ↔
    x ∈ F.points X t
  have hx : (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (Over.mk t.left)).symm
      (ParameterPointTransport.parameterPointMulEquiv G P X t x) = e.hom ≫ x :=
    (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (Over.mk t.left)).symm_apply_apply _
  rw [hx, ht]
  exact relativeSubgroup_membership_iso F e t x

private theorem pow_eq_one_of_equiv {M N : Type*} [Monoid M] [Monoid N]
    (e : M ≃* N) (n : ℕ) (x : M) (h : (e x) ^ n = 1) : x ^ n = 1 := by
  apply e.injective
  simpa only [map_pow, map_one] using h

theorem relativeSubgroupFromParameter_killed
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup ((Over.pullback P.hom).obj G.X) (Over.mk (𝟙 P.left)))
    (n : ℕ) (h : F.KilledBy n) : (relativeSubgroupFromParameter G P F).KilledBy n := by
  intro X t x hx
  exact @pow_eq_one_of_equiv _ _
    CategoryTheory.Hom.monoid CategoryTheory.Hom.monoid
    (ParameterPointTransport.parameterPointMulEquiv G P X t) n x
    (h (Over.mk t.left) (terminalParameterPoint (Over.mk t.left))
      (ParameterPointTransport.parameterPointMulEquiv G P X t x) hx)

def relativeSubgroupFromParameterPointEquiv
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup ((Over.pullback P.hom).obj G.X) (Over.mk (𝟙 P.left)))
    (X : Over S) (t : X ⟶ P) :
    (relativeSubgroupFromParameter G P F).points X t ≃*
      F.points (Over.mk t.left) (terminalParameterPoint (Over.mk t.left)) where
  toFun x := ⟨ParameterPointTransport.parameterPointMulEquiv G P X t x.val, x.property⟩
  invFun x := ⟨(ParameterPointTransport.parameterPointMulEquiv G P X t).symm x.val, by
    change ParameterPointTransport.parameterPointMulEquiv G P X t ((ParameterPointTransport.parameterPointMulEquiv G P X t).symm x.val) ∈
      F.points (Over.mk t.left) (terminalParameterPoint (Over.mk t.left))
    rw [MulEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext ((ParameterPointTransport.parameterPointMulEquiv G P X t).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((ParameterPointTransport.parameterPointMulEquiv G P X t).apply_symm_apply x.val)
  map_mul' x y := Subtype.ext ((ParameterPointTransport.parameterPointMulEquiv G P X t).map_mul x.val y.val)

theorem relativeSubgroupFromParameter_moduleType
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup ((Over.pullback P.hom).obj G.X) (Over.mk (𝟙 P.left)))
    (M : Type u) [AddCommGroup M] (h : F.HasModuleType M) :
    (relativeSubgroupFromParameter G P F).HasModuleType M := by
  intro k _ _ b t
  obtain ⟨e⟩ := h k t.left (terminalParameterPoint (Over.mk t.left))
  exact ⟨(relativeSubgroupFromParameterPointEquiv G P F (Over.mk b) t).trans e⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.SubgroupFromParameter
