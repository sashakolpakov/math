import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineGlobalExact
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-! # Module Sheaf Injectives -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSheafInjectives.Construction

noncomputable section

/-! Enough injectives for sheaves of modules on a topological space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u

variable (R : Type u) [CommRing R] (X : TopCat.{u})

abbrev ModuleSheaves :=
  CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X) (ModuleCat.{u} R)

abbrev moduleSheafStalk (x : X) : ModuleSheaves R X ⥤ ModuleCat.{u} R :=
  sheafToPresheaf _ _ ⋙ TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x

def moduleSheafSkyscraper (x : X) : ModuleCat.{u} R ⥤ ModuleSheaves R X := by
  classical
  exact skyscraperSheafFunctor x

def moduleSheafStalkAdjunction (x : X) :
    moduleSheafStalk R X x ⊣ moduleSheafSkyscraper R X x := by
  classical
  exact stalkSkyscraperSheafAdjunction x

instance moduleSheafStalk_preservesMonos (x : X) :
    (moduleSheafStalk R X x).PreservesMonomorphisms :=
  TopCat.Presheaf.stalkFunctor_preserves_mono x

theorem injective_moduleSheafSkyscraper (x : X) (I : ModuleCat.{u} R) [Injective I] :
    Injective ((moduleSheafSkyscraper R X x).obj I) :=
  Injective.injective_of_adjoint (moduleSheafStalkAdjunction R X x) I

variable (F : ModuleSheaves R X)

abbrev moduleSheafInjectiveFamily (x : X) : ModuleSheaves R X :=
  (moduleSheafSkyscraper R X x).obj (Injective.under ((moduleSheafStalk R X x).obj F))

instance moduleSheafInjectiveFamily_injective (x : X) :
    Injective (moduleSheafInjectiveFamily R X F x) :=
  injective_moduleSheafSkyscraper R X x _

def moduleSheafToInjectiveFactor (x : X) : F ⟶ moduleSheafInjectiveFamily R X F x :=
  (moduleSheafStalkAdjunction R X x).homEquiv _ _
    (Injective.ι ((moduleSheafStalk R X x).obj F))

theorem moduleSheafToInjectiveFactor_counit (x : X) :
    (moduleSheafStalk R X x).map (moduleSheafToInjectiveFactor R X F x) ≫
      (moduleSheafStalkAdjunction R X x).counit.app
        (Injective.under ((moduleSheafStalk R X x).obj F)) =
      Injective.ι ((moduleSheafStalk R X x).obj F) := by
  exact ((moduleSheafStalkAdjunction R X x).homEquiv_counit F
    (Injective.under ((moduleSheafStalk R X x).obj F))
    (moduleSheafToInjectiveFactor R X F x)).symm.trans
      ((moduleSheafStalkAdjunction R X x).homEquiv _ _ |>.symm_apply_apply _)

def moduleSheafToInjective : F ⟶ ∏ᶜ moduleSheafInjectiveFamily R X F :=
  Pi.lift (moduleSheafToInjectiveFactor R X F)

theorem mono_moduleSheafToInjective_stalk (x : X) :
    Mono ((moduleSheafStalk R X x).map (moduleSheafToInjective R X F)) := by
  have h : (moduleSheafStalk R X x).map (moduleSheafToInjective R X F) ≫
      ((moduleSheafStalk R X x).map (Pi.π (moduleSheafInjectiveFamily R X F) x) ≫
        (moduleSheafStalkAdjunction R X x).counit.app
          (Injective.under ((moduleSheafStalk R X x).obj F))) =
      Injective.ι ((moduleSheafStalk R X x).obj F) := by
    rw [← Category.assoc, ← Functor.map_comp]
    change (moduleSheafStalk R X x).map
      (Pi.lift (moduleSheafToInjectiveFactor R X F) ≫ Pi.π _ x) ≫ _ = _
    rw [Pi.lift_comp_π]
    exact moduleSheafToInjectiveFactor_counit R X F x
  exact mono_of_mono_fac h

instance moduleSheafToInjective_mono : Mono (moduleSheafToInjective R X F) := by
  have hx (x : X) : Mono ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map
      (moduleSheafToInjective R X F).hom) := mono_moduleSheafToInjective_stalk R X F x
  exact TopCat.Presheaf.mono_of_stalk_mono (moduleSheafToInjective R X F)

def moduleSheafInjectivePresentation : InjectivePresentation F where
  J := ∏ᶜ moduleSheafInjectiveFamily R X F
  f := moduleSheafToInjective R X F

theorem moduleSheaves_enoughInjectives : EnoughInjectives (ModuleSheaves R X) where
  presentation F := ⟨moduleSheafInjectivePresentation R X F⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSheafInjectives.Construction
