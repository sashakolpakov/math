import Mathlib.Topology.Sheaves.Functors

/-! # Vanishing -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Vanishing.Projective.TopCat

open _root_.TopCat

/-!
# Native site sheaves for the ProjectiveCohomology vanishing development

These abbreviations use the same category of site sheaves as ProjectiveCohomology's cohomology.
They avoid the extra category wrapper on `TopCat.Sheaf` in the current library.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe w v u

abbrev Sheaf (C : Type u) [Category.{v} C] (X : _root_.TopCat.{w}) :=
  CategoryTheory.Sheaf (Opens.grothendieckTopology X) C

namespace Sheaf
open _root_.TopCat.Sheaf

variable (C : Type u) [Category.{v} C] {X Y : _root_.TopCat.{w}}

abbrev forget (X : _root_.TopCat.{w}) :=
  sheafToPresheaf (Opens.grothendieckTopology X) C

abbrev pushforward (f : X ⟶ Y) : Projective.TopCat.Sheaf C X ⥤ Projective.TopCat.Sheaf C Y :=
  (Opens.map f).sheafPushforwardContinuous C _ _

noncomputable def isTerminalOfEmpty (F : Projective.TopCat.Sheaf C X) : IsTerminal (F.obj.obj (.op ⊥)) :=
  F.isTerminalOfBotCover ⊥ (fun _ h => h.elim)

variable (A : Type*) [Category.{w} A] {FA : A → A → Type*} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
variable [HasColimits A] [HasLimits A] [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

noncomputable abbrev pullback (f : X ⟶ Y) : Projective.TopCat.Sheaf A Y ⥤ Projective.TopCat.Sheaf A X :=
  (Opens.map f).sheafPullback A _ _

noncomputable def pullbackIso (f : X ⟶ Y) :
    Projective.TopCat.Sheaf.pullback A f ≅ Projective.TopCat.Sheaf.forget A Y ⋙ _root_.TopCat.Presheaf.pullback A f ⋙
      presheafToSheaf _ _ :=
  Functor.sheafPullbackConstruction.sheafPullbackIso _ _ _ _

noncomputable abbrev pullbackPushforwardAdjunction (f : X ⟶ Y) :
    Projective.TopCat.Sheaf.pullback A f ⊣ pushforward A f :=
  (Opens.map f).sheafAdjunctionContinuous A _ _

instance (f : X ⟶ Y) : (Projective.TopCat.Sheaf.pullback A f).IsLeftAdjoint :=
  (pullbackPushforwardAdjunction A f).isLeftAdjoint

instance (f : X ⟶ Y) : (pushforward A f).IsRightAdjoint :=
  (pullbackPushforwardAdjunction A f).isRightAdjoint

end Sheaf

end OAI.AlgebraicGeometry.SheafCohomology.Vanishing.Projective.TopCat
