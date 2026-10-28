import OAI.AlgebraicGeometry.Comparison.Betti.StalkToPointModule
import OAI.AlgebraicGeometry.Comparison.Betti.PointModuleToStalk

/-! # Stalk Point Module Adjunction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.StalkPointModuleAdjunction.Local

noncomputable section

section

/-! The actual stalk and point-supported module constructions satisfy
the expected hom-set equivalence, with both inverse laws proved on
the original section germs. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} (R : TopCat.Presheaf RingCat.{0} X) (x : X)

def stalkPointModuleHomEquiv (M : PresheafOfModules.{0} R) (N : ModuleCat.{0} (R.stalk x)) :
    ((RingModuleStalkFunctor.Local.ringModuleStalk R x).obj M ⟶ N) ≃ (M ⟶ PointModulePresheaf.Local.pointModulePresheaf R x N) where
  toFun := StalkToPointModule.Local.stalkToPointModuleHom x M N
  invFun := PointModuleToStalk.Local.pointModuleHomToStalk x M N
  left_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat) (X := X) M.presheaf m
    exact PointModuleToStalk.Local.pointModuleHomToStalkAdd_germ x M N (StalkToPointModule.Local.stalkToPointModuleHom x M N f) U hxU a
  right_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    funext hx
    exact PointModuleToStalk.Local.pointModuleHomToStalkAdd_germ x M N f U.unop hx.down m

theorem stalkPointModuleHomEquiv_naturality_left
    {M M' : PresheafOfModules.{0} R} {N : ModuleCat.{0} (R.stalk x)}
    (f : M ⟶ M') (g : (RingModuleStalkFunctor.Local.ringModuleStalk R x).obj M' ⟶ N) :
    stalkPointModuleHomEquiv R x M N ((RingModuleStalkFunctor.Local.ringModuleStalk R x).map f ≫ g) =
      f ≫ stalkPointModuleHomEquiv R x M' N g := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  funext hx
  exact congrArg g (RingModuleStalkMap.Local.ringModuleStalkMap_germ f x U.unop hx.down m)

theorem stalkPointModuleHomEquiv_naturality_right
    {M : PresheafOfModules.{0} R} {N N' : ModuleCat.{0} (R.stalk x)}
    (f : (RingModuleStalkFunctor.Local.ringModuleStalk R x).obj M ⟶ N) (g : N ⟶ N') :
    stalkPointModuleHomEquiv R x M N' (f ≫ g) =
      stalkPointModuleHomEquiv R x M N f ≫ (PointModuleFunctor.Local.pointModulePresheafFunctor R x).map g := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  funext hx
  rfl

theorem stalkPointModuleHomEquiv_naturality_left_symm
    {M M' : PresheafOfModules.{0} R} {N : ModuleCat.{0} (R.stalk x)}
    (f : M ⟶ M') (g : M' ⟶ PointModulePresheaf.Local.pointModulePresheaf R x N) :
    (stalkPointModuleHomEquiv R x M N).symm (f ≫ g) =
      (RingModuleStalkFunctor.Local.ringModuleStalk R x).map f ≫ (stalkPointModuleHomEquiv R x M' N).symm g := by
  apply (stalkPointModuleHomEquiv R x M N).injective
  erw [Equiv.apply_symm_apply, stalkPointModuleHomEquiv_naturality_left, Equiv.apply_symm_apply]

end

/-! Actual module stalks are left adjoint to point-supported module
presheaves and sheaves. The adjunction uses the original section germs. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable {X : TopCat.{0}}

def stalkPointModuleAdjunction (R : TopCat.Presheaf RingCat.{0} X) (x : X) :
    RingModuleStalkFunctor.Local.ringModuleStalk R x ⊣ PointModuleFunctor.Local.pointModulePresheafFunctor R x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := stalkPointModuleHomEquiv R x
      homEquiv_naturality_left_symm := stalkPointModuleHomEquiv_naturality_left_symm R x
      homEquiv_naturality_right := stalkPointModuleHomEquiv_naturality_right R x }

instance ringModuleStalk_isLeftAdjoint (R : TopCat.Presheaf RingCat.{0} X) (x : X) :
    (RingModuleStalkFunctor.Local.ringModuleStalk R x).IsLeftAdjoint := (stalkPointModuleAdjunction R x).isLeftAdjoint

def sheafRingModuleStalk (R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}) (x : X) :
    SheafOfModules.{0} R ⥤ ModuleCat.{0} (TopCat.Presheaf.stalk (C := RingCat) (X := X) R.obj x) :=
  SheafOfModules.forget R ⋙ RingModuleStalkFunctor.Local.ringModuleStalk R.obj x

def stalkPointModuleSheafHomEquiv (R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}) (x : X)
    (M : SheafOfModules.{0} R) (N : ModuleCat.{0} (TopCat.Presheaf.stalk (C := RingCat) (X := X) R.obj x)) :
    ((sheafRingModuleStalk R x).obj M ⟶ N) ≃ (M ⟶ (PointModuleFunctor.Local.pointModuleSheafFunctor R x).obj N) where
  toFun f := ⟨StalkToPointModule.Local.stalkToPointModuleHom x M.val N f⟩
  invFun f := PointModuleToStalk.Local.pointModuleHomToStalk x M.val N f.val
  left_inv f := (stalkPointModuleHomEquiv R.obj x M.val N).left_inv f
  right_inv f := SheafOfModules.Hom.ext ((stalkPointModuleHomEquiv R.obj x M.val N).right_inv f.val)

def stalkPointModuleSheafAdjunction (R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}) (x : X) :
    sheafRingModuleStalk R x ⊣ PointModuleFunctor.Local.pointModuleSheafFunctor R x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := stalkPointModuleSheafHomEquiv R x
      homEquiv_naturality_left_symm := by
        intro M M' N f g
        exact stalkPointModuleHomEquiv_naturality_left_symm R.obj x f.val g.val
      homEquiv_naturality_right := by
        intro M N N' f g
        apply SheafOfModules.Hom.ext
        exact stalkPointModuleHomEquiv_naturality_right R.obj x f g }

instance sheafRingModuleStalk_isLeftAdjoint (R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}) (x : X) :
    (sheafRingModuleStalk R x).IsLeftAdjoint := (stalkPointModuleSheafAdjunction R x).isLeftAdjoint

end

end OAI.AlgebraicGeometry.Comparison.Betti.StalkPointModuleAdjunction.Local
