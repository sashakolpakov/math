import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSheafInjectives
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-! # Abelian Sheaf Injectives -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction

noncomputable section

/-! Enough injectives for sheaves of abelian groups on a topological space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u

variable (X : TopCat.{u})

abbrev AbelianSheaves :=
  CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X) (AddCommGrpCat.{u})

abbrev abelianSheafStalk (x : X) : AbelianSheaves X ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf _ _ ⋙ TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{u}) x

def abelianSheafSkyscraper (x : X) : AddCommGrpCat.{u} ⥤ AbelianSheaves X := by
  classical
  exact skyscraperSheafFunctor x

def abelianSheafStalkAdjunction (x : X) :
    abelianSheafStalk X x ⊣ abelianSheafSkyscraper X x := by
  classical
  exact stalkSkyscraperSheafAdjunction x

instance abelianSheafStalk_preservesMonos (x : X) :
    (abelianSheafStalk X x).PreservesMonomorphisms :=
  TopCat.Presheaf.stalkFunctor_preserves_mono x

theorem injective_abelianSheafSkyscraper (x : X) (I : AddCommGrpCat.{u}) [Injective I] :
    Injective ((abelianSheafSkyscraper X x).obj I) :=
  Injective.injective_of_adjoint (abelianSheafStalkAdjunction X x) I

variable (F : AbelianSheaves X)

abbrev abelianSheafInjectiveFamily (x : X) : AbelianSheaves X :=
  (abelianSheafSkyscraper X x).obj (Injective.under ((abelianSheafStalk X x).obj F))

instance abelianSheafInjectiveFamily_injective (x : X) :
    Injective (abelianSheafInjectiveFamily X F x) :=
  injective_abelianSheafSkyscraper X x _

def abelianSheafToInjectiveFactor (x : X) : F ⟶ abelianSheafInjectiveFamily X F x :=
  (abelianSheafStalkAdjunction X x).homEquiv _ _
    (Injective.ι ((abelianSheafStalk X x).obj F))

theorem abelianSheafToInjectiveFactor_counit (x : X) :
    (abelianSheafStalk X x).map (abelianSheafToInjectiveFactor X F x) ≫
      (abelianSheafStalkAdjunction X x).counit.app
        (Injective.under ((abelianSheafStalk X x).obj F)) =
      Injective.ι ((abelianSheafStalk X x).obj F) := by
  exact ((abelianSheafStalkAdjunction X x).homEquiv_counit F
    (Injective.under ((abelianSheafStalk X x).obj F))
    (abelianSheafToInjectiveFactor X F x)).symm.trans
      ((abelianSheafStalkAdjunction X x).homEquiv _ _ |>.symm_apply_apply _)

def abelianSheafToInjective : F ⟶ ∏ᶜ abelianSheafInjectiveFamily X F :=
  Pi.lift (abelianSheafToInjectiveFactor X F)

theorem mono_abelianSheafToInjective_stalk (x : X) :
    Mono ((abelianSheafStalk X x).map (abelianSheafToInjective X F)) := by
  have h : (abelianSheafStalk X x).map (abelianSheafToInjective X F) ≫
      ((abelianSheafStalk X x).map (Pi.π (abelianSheafInjectiveFamily X F) x) ≫
        (abelianSheafStalkAdjunction X x).counit.app
          (Injective.under ((abelianSheafStalk X x).obj F))) =
      Injective.ι ((abelianSheafStalk X x).obj F) := by
    rw [← Category.assoc, ← Functor.map_comp]
    change (abelianSheafStalk X x).map
      (Pi.lift (abelianSheafToInjectiveFactor X F) ≫ Pi.π _ x) ≫ _ = _
    rw [Pi.lift_comp_π]
    exact abelianSheafToInjectiveFactor_counit X F x
  exact mono_of_mono_fac h

instance abelianSheafToInjective_mono : Mono (abelianSheafToInjective X F) := by
  have hx (x : X) : Mono ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{u}) x).map
      (abelianSheafToInjective X F).hom) := mono_abelianSheafToInjective_stalk X F x
  exact TopCat.Presheaf.mono_of_stalk_mono (abelianSheafToInjective X F)

def abelianSheafInjectivePresentation : InjectivePresentation F where
  J := ∏ᶜ abelianSheafInjectiveFamily X F
  f := abelianSheafToInjective X F

theorem abelianSheaves_enoughInjectives : EnoughInjectives (AbelianSheaves X) where
  presentation F := ⟨abelianSheafInjectivePresentation X F⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction
