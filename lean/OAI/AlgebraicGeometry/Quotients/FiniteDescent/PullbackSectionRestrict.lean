import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Pullback Section Restrict -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionRestrict

noncomputable section

/-! The canonical semilinear pullback of local sections and its restriction compatibility. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u

namespace Construction.PullbackSectionCoefficients

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)

def map (U : X.Opens) : Γ(M, U) →ₛₗ[(f.app U).hom]
    Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) where
  toFun := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U)
  map_add' := (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U)).hom.map_add
  map_smul' r x :=
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U)).hom.map_smul r x

theorem restrict {U V : X.Opens} (h : V ≤ U) (s : Γ(M, U)) :
    PullbackSectionCoefficients.map f M V (M.presheaf.map (homOfLE h).op s) =
      ((Scheme.Modules.pullback f).obj M).presheaf.map
        ((TopologicalSpace.Opens.map f.base).map (homOfLE h)).op (PullbackSectionCoefficients.map f M U s) :=
  (PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val (homOfLE h).op s)

theorem naturality {M N : X.Modules} (a : M ⟶ N) (U : X.Opens) (s : Γ(M, U)) :
    PullbackSectionCoefficients.map f N U (a.val.app (op U) s) =
      ((Scheme.Modules.pullback f).map a).val.app (op (f ⁻¹ᵁ U)) (PullbackSectionCoefficients.map f M U s) := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a
  have h' := congrArg (fun z => z.val.app (op U)) h
  exact ConcreteCategory.congr_hom h' s

end Construction.PullbackSectionCoefficients

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionRestrict
