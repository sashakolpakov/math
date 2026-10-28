import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.Functors
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CohomologyCoverModule
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CohomologyExact

/-! # Additive Sheaf Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling

noncomputable section

universe u
open _root_.CategoryTheory Limits Opposite _root_.TopologicalSpace _root_.AlgebraicGeometry

abbrev AbSheaf (X : Scheme.{u}) :=
  CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

abbrev ExtH {X : Scheme.{u}}
    (F : AbSheaf X) (n : ℕ) : Type u :=
  Abelian.Ext
    ((CategoryTheory.constantSheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))) F n

noncomputable def openSheafPullback
    {X : Scheme.{u}} (U : X.Opens) :
    AbSheaf X ⥤ AbSheaf U :=
  U.ι.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}

noncomputable def openSheafPushforward
    {X : Scheme.{u}} (U : X.Opens) :
    AbSheaf U ⥤ AbSheaf X :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{u} U.ι.base

noncomputable def openRestrictionPushforward
    {X : Scheme.{u}} (U : X.Opens) :
    AbSheaf X ⥤ AbSheaf X :=
  openSheafPullback U ⋙ openSheafPushforward U

noncomputable def openRestrictionPushforwardUnit
    {X : Scheme.{u}} (U : X.Opens) :
    𝟭 (AbSheaf X) ⟶
      openRestrictionPushforward U where
  app F :=
    { hom :=
        { app V := F.1.map
            (homOfLE (U.ι.image_preimage_le V.unop)).op
          naturality := by
            intro V W i
            change F.1.map i ≫ F.1.map _ =
              F.1.map _ ≫ F.1.map _
            calc
              _ = F.1.map (i ≫ _) := (F.1.map_comp _ _).symm
              _ = F.1.map (_ ≫ _) := congrArg F.1.map (Subsingleton.elim _ _)
              _ = _ := F.1.map_comp _ _ } }
  naturality F G f := by
    apply CategoryTheory.Sheaf.hom_ext
    ext V x
    change (f.hom.app V ≫ G.1.map _).hom x =
      (F.1.map _ ≫ f.hom.app _).hom x
    exact congrArg (fun k ↦ k.hom x)
      (f.hom.naturality
        (homOfLE (U.ι.image_preimage_le V.unop)).op).symm

noncomputable def openRestrictionPushforwardSection
    {X : Scheme.{u}} (U : X.Opens) (F : AbSheaf X)
    (t : F.1.obj (op U)) :
    ((openRestrictionPushforward U).obj F).1.obj
      (op (⊤ : Opens X)) := by
  let W := U.ι.isOpenEmbedding.functor.obj
    ((Opens.map U.ι.base).obj (⊤ : Opens X))
  change F.1.obj (op W)
  have hW : W = U := by
    ext x
    simp [W]
  exact F.1.map (eqToHom hW).op t

theorem openRestrictionPushforwardSection_map
    {X : Scheme.{u}} (U : X.Opens) {F G : AbSheaf X}
    (f : F ⟶ G) (t : F.1.obj (op U)) :
    (((openRestrictionPushforward U).map f).hom.app (op (⊤ : Opens X)))
        (openRestrictionPushforwardSection U F t) =
      openRestrictionPushforwardSection U G (f.hom.app (op U) t) := by
  let W := U.ι.isOpenEmbedding.functor.obj
    ((Opens.map U.ι.base).obj (⊤ : Opens X))
  have hW : W = U := by
    ext x
    simp [W]
  change f.hom.app (op W) (F.1.map (eqToHom hW).op t) =
    G.1.map (eqToHom hW).op (f.hom.app (op U) t)
  exact congrArg (fun k ↦ k.hom t)
    (f.hom.naturality (eqToHom hW).op)

theorem openRestrictionPushforwardUnit_section
    {X : Scheme.{u}} (U : X.Opens) (F : AbSheaf X)
    (s : F.1.obj (op (⊤ : Opens X))) :
    ((openRestrictionPushforwardUnit U).app F).hom.app
        (op (⊤ : Opens X)) s =
      openRestrictionPushforwardSection U F
        (F.1.map (homOfLE le_top).op s) := by
  have hW : U.ι ''ᵁ (U.ι ⁻¹ᵁ (⊤ : Opens X)) = U := by
    ext x
    simp
  change F.1.map (homOfLE (U.ι.image_preimage_le (⊤ : Opens X))).op s =
    F.1.map (eqToHom hW).op (F.1.map (homOfLE le_top).op s)
  have hk : (homOfLE (U.ι.image_preimage_le (⊤ : Opens X))).op =
      (homOfLE le_top).op ≫ (eqToHom hW).op :=
    Subsingleton.elim _ _
  rw [hk, F.1.map_comp, ConcreteCategory.comp_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.AdditiveSheafRestriction.ZariskiCohomology.LocalKilling
