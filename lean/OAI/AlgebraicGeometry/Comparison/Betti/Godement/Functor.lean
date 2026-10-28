import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GodementEmbedding
import OAI.AlgebraicGeometry.Comparison.Betti.Module.StalkExactFunctor

/-! # Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.Functor

noncomputable section

/-! The genuine sheaf of all stalk-value families is an additive
functor, with the original natural monomorphism into a flasque sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.TopCat.Presheaf

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions

variable {X : TopCat.{0}}

def stalkFamilyMap {F G : TopCat.Sheaf (ModuleCat.{0} ℂ) X} (f : F ⟶ G) :
    HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf F ⟶ HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf G :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom
        { toFun := fun s x => (stalkFunctor (ModuleCat.{0} ℂ) x.val).map f.hom (s x)
          map_add' := by intro s t; funext x; exact map_add _ _ _
          map_smul' := by intro c s; funext x; exact map_smul _ _ _ }
      naturality := by
        intro U V i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        funext x
        rfl }

def stalkFamilyFunctor (X : TopCat.{0}) : TopCat.Sheaf (ModuleCat.{0} ℂ) X ⥤ TopCat.Sheaf (ModuleCat.{0} ℂ) X where
  obj := HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf
  map := stalkFamilyMap
  map_id F := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    funext x
    change (stalkFunctor (ModuleCat.{0} ℂ) x.val).map (𝟙 F.obj) (s x) = s x
    erw [CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    funext x
    change (stalkFunctor (ModuleCat.{0} ℂ) x.val).map (f.hom ≫ g.hom) (s x) =
      (stalkFunctor (ModuleCat.{0} ℂ) x.val).map g.hom
        ((stalkFunctor (ModuleCat.{0} ℂ) x.val).map f.hom (s x))
    erw [CategoryTheory.Functor.map_comp]
    rfl

instance stalkFamilyFunctor_additive : (stalkFamilyFunctor X).Additive where
  map_add {F G} f g := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    funext x
    have hp : PreservesFiniteLimits (stalkFunctor (ModuleCat.{0} ℂ) x.val) :=
      Module.StalkExactFunctor.Holomorphic.moduleStalk_preservesFiniteLimits (X := X) x.val
    have h : (stalkFunctor (ModuleCat.{0} ℂ) x.val).Additive :=
      (stalkFunctor (ModuleCat.{0} ℂ) x.val).additive_of_preserves_binary_products
    change (stalkFunctor (ModuleCat.{0} ℂ) x.val).map (f.hom + g.hom) (s x) =
      (stalkFunctor (ModuleCat.{0} ℂ) x.val).map f.hom (s x) +
        (stalkFunctor (ModuleCat.{0} ℂ) x.val).map g.hom (s x)
    erw [CategoryTheory.Functor.map_add]
    rfl

def stalkFamilyUnit (X : TopCat.{0}) : 𝟭 (TopCat.Sheaf (ModuleCat.{0} ℂ) X) ⟶ stalkFamilyFunctor X where
  app := HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilyEmbedding
  naturality {F G} f := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    funext x
    exact (stalkFunctor_map_germ_apply U.unop x.val x.property f.hom s).symm

theorem stalkFamilyUnit_mono (F : TopCat.Sheaf (ModuleCat.{0} ℂ) X) :
    Mono ((stalkFamilyUnit X).app F) := HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilyEmbedding_mono F

theorem stalkFamilyFunctor_isFlasque (F : TopCat.Sheaf (ModuleCat.{0} ℂ) X) :
    TopCat.Sheaf.IsFlasque ((stalkFamilyFunctor X).obj F) := HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions.stalkFamilySheaf_isFlasque F

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.Functor
