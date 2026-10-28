import OAI.AlgebraicGeometry.Comparison.Betti.RingModuleStalkMap
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.AB

/-! # Ring Module Stalk Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.RingModuleStalkFunctor.Local

noncomputable section

/-! The actual module stalks form an additive functor to modules over
the ring stalk; forgetting scalars gives the original abelian stalk. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} (R : TopCat.Presheaf RingCat.{0} X) (x : X)

def ringModuleStalk : PresheafOfModules.{0} R ⥤ ModuleCat.{0} (R.stalk x) where
  obj M := ModuleCat.of (R.stalk x) (TopCat.Presheaf.stalk (C := AddCommGrpCat) (X := X) M.presheaf x)
  map f := ModuleCat.ofHom (RingModuleStalkMap.Local.ringModuleStalkMap f x)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact ConcreteCategory.congr_hom
      ((PresheafOfModules.toPresheaf R ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_id M) m
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact ConcreteCategory.congr_hom
      ((PresheafOfModules.toPresheaf R ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_comp f g) m

instance ringModuleStalk_additive : (ringModuleStalk R x).Additive := by
  constructor
  intro M N f g
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  have h₁ := congrArg (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf R).map_add (f := f) (g := g))
  have h₂ := (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_add
    (f := (PresheafOfModules.toPresheaf R).map f) (g := (PresheafOfModules.toPresheaf R).map g)
  exact ConcreteCategory.congr_hom (h₁.trans h₂) m

def ringModuleStalkForgetIso :
    ringModuleStalk R x ⋙ forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat ≅
      PresheafOfModules.toPresheaf R ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat x :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

end

end OAI.AlgebraicGeometry.Comparison.Betti.RingModuleStalkFunctor.Local
