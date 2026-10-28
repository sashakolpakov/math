import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackModuleSections
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Open Pullback Sections -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenPullbackSections.Construction

noncomputable section

/-! Pullback to an open subscheme gives the original module sections on that open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

def modulePullbackSection {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) :
    Γ(M, U) →+ Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U).hom

theorem modulePullbackSection_smul {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (r : Γ(Y, U)) (m : Γ(M, U)) :
    modulePullbackSection f M U (r • m) = f.app U r • modulePullbackSection f M U m :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app_smul r m

theorem openPullback_unit_app_isIso {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app M).app U) := by
  have he : U.ι ''ᵁ (U.ι ⁻¹ᵁ U) = U := by rw [U.ι_preimage_self, U.ι_image_top]
  have hh : homOfLE (U.ι.image_preimage_le U) = eqToHom he := Subsingleton.elim _ _
  have hr : IsIso (((Scheme.Modules.restrictAdjunction U.ι).unit.app M).app U) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    rw [hh]
    exact (M.presheaf.mapIso (eqToIso he).op).isIso_hom
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction U.ι) (Scheme.Modules.pullbackPushforwardAdjunction U.ι) M
  have hc := congrArg (fun q : M ⟶ (Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.pullback U.ι).obj M) ↦ q.app U) h
  change ((Scheme.Modules.restrictAdjunction U.ι).unit.app M).app U ≫
    ((Scheme.Modules.pushforward U.ι).map ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app M)).app U =
      ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app M).app U at hc
  rw [← hc]
  infer_instance

def moduleOpenPullbackSectionsMap {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Γ(M, U) →+ Γ((Scheme.Modules.pullback U.ι).obj M, ⊤) :=
  (((Scheme.Modules.pullback U.ι).obj M).presheaf.map (eqToHom U.ι_preimage_self.symm).op).hom.comp
    (modulePullbackSection U.ι M U)

theorem moduleOpenPullbackSectionsMap_smul {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) (m : Γ(M, U)) :
    moduleOpenPullbackSectionsMap M U (r • m) =
      U.ι.appLE U ⊤ U.ι_preimage_self.ge r • moduleOpenPullbackSectionsMap M U m := by
  change ((Scheme.Modules.pullback U.ι).obj M).presheaf.map (eqToHom U.ι_preimage_self.symm).op
    (modulePullbackSection U.ι M U (r • m)) = _
  rw [modulePullbackSection_smul, Scheme.Modules.map_smul]
  rfl

theorem moduleOpenPullbackSectionsMap_bijective {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Function.Bijective (moduleOpenPullbackSectionsMap M U) := by
  have hunit := openPullback_unit_app_isIso M U
  exact (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullback U.ι).obj M).presheaf.map (eqToHom U.ι_preimage_self.symm).op)).comp
      (ConcreteCategory.bijective_of_isIso
        (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app M).app U))

def moduleOpenPullbackSectionsEquiv {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Γ(M, U) ≃+ Γ((Scheme.Modules.pullback U.ι).obj M, ⊤) :=
  AddEquiv.ofBijective (moduleOpenPullbackSectionsMap M U) (moduleOpenPullbackSectionsMap_bijective M U)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenPullbackSections.Construction
