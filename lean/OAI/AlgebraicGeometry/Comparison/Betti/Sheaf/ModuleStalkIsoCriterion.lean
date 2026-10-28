import OAI.AlgebraicGeometry.Comparison.Betti.Module.StalkExact

/-! # Module Stalk Iso Criterion -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.ModuleStalkIsoCriterion.Local

noncomputable section

/-! Native module stalks detect isomorphisms of sheaves of modules. -/

open _root_.CategoryTheory _root_.TopologicalSpace

theorem sheafModule_isIso_of_stalk_isIso {X : TopCat.{0}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}
    {M N : SheafOfModules.{0} R} (f : M ⟶ N)
    (hf : ∀ x, IsIso ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk R x).map f)) : IsIso f := by
  have hAb (x : X) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
      ((SheafOfModules.toSheaf.{0} R).map f).hom) := by
    have := hf x
    change IsIso ((forget₂ (ModuleCat (TopCat.Presheaf.stalk (C := RingCat) (X := X) R.obj x))
      AddCommGrpCat.{0}).map ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk R x).map f))
    infer_instance
  have : IsIso ((SheafOfModules.toSheaf.{0} R).map f) :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso ((SheafOfModules.toSheaf.{0} R).map f)
  exact isIso_of_reflects_iso f (SheafOfModules.toSheaf.{0} R)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.ModuleStalkIsoCriterion.Local
