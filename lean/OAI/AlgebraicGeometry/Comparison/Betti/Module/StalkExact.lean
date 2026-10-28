import OAI.AlgebraicGeometry.Comparison.Betti.StalkPointModuleAdjunction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # Stalk Exact -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.StalkExact.Local

noncomputable section

section

/-! The actual module stalk functors preserve finite limits and
colimits. Their underlying abelian stalks detect monomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X : TopCat.{0}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}) (x : X)

def sheafRingModuleStalkForgetIso :
    StalkPointModuleAdjunction.Local.sheafRingModuleStalk R x ⋙
        forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat) (X := X) R.obj x)) AddCommGrpCat.{0} ≅
      SheafOfModules.toSheaf.{0} R ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

instance sheafRingModuleStalk_preservesFiniteLimits :
    PreservesFiniteLimits (StalkPointModuleAdjunction.Local.sheafRingModuleStalk R x) := by
  have hStalk : PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x) := inferInstance
  have : PreservesFiniteLimits (SheafOfModules.toSheaf.{0} R ⋙
      (TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x)) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _ (SheafOfModules.toSheaf.{0} R)
      (TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x)
      inferInstance hStalk
  have := preservesFiniteLimits_of_natIso (sheafRingModuleStalkForgetIso R x).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (StalkPointModuleAdjunction.Local.sheafRingModuleStalk R x)
    (forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat) (X := X) R.obj x)) AddCommGrpCat.{0})

instance sheafRingModuleStalk_preservesFiniteColimits :
    PreservesFiniteColimits (StalkPointModuleAdjunction.Local.sheafRingModuleStalk R x) := inferInstance

end

/-! Monomorphisms of actual sheaves of modules are detected by all
their native module stalks. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable {X : TopCat.{0}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}

theorem sheafModule_mono_of_stalk_mono {M N : SheafOfModules.{0} R} (f : M ⟶ N)
    (hf : ∀ x, Mono ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk R x).map f)) : Mono f := by
  have hAb (x : X) : Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
      ((SheafOfModules.toSheaf.{0} R).map f).hom) := by
    have := hf x
    change Mono ((forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat) (X := X) R.obj x))
      AddCommGrpCat.{0}).map ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk R x).map f))
    infer_instance
  exact (SheafOfModules.toSheaf.{0} R).mono_of_mono_map
    (TopCat.Presheaf.mono_of_stalk_mono ((SheafOfModules.toSheaf.{0} R).map f))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Module.StalkExact.Local
