import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange
import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.PresheafContraction
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.Pullback

/-! # Cech Restriction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.CechRestriction.MixedCechRestriction

noncomputable section

/-!
Mixed-universe version for the native crystalline coefficient modules.

# Restricting the global Čech presheaf complex

The restriction of the global complex to an open subscheme is identified
with the complex of the inverse-image family. This connects the global
construction to the proved local contractions.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

universe u v

variable (R : Type v) [CommRing R] {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

def restrictionFunctor : Presheaf.MixedCechPresheaf.Presheaves R X ⥤ Presheaf.MixedCechPresheaf.Presheaves R Y :=
  (Functor.whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ (ModuleCat.{max u v} R)).obj f.opensFunctor.op

instance restriction_additive : (restrictionFunctor R f).Additive := by
  dsimp [restrictionFunctor]
  infer_instance

instance restriction_preservesLimits : PreservesLimitsOfSize.{u, u} (restrictionFunctor R f) := by
  dsimp [restrictionFunctor]
  infer_instance

def preimageFunctor : X.Opens ⥤ Y.Opens := TopologicalSpace.Opens.map f.base

instance preimage_rightAdjoint : (preimageFunctor f).IsRightAdjoint :=
  f.opensFunctorAdjunction.isRightAdjoint

instance preimage_preservesFiniteLimits : PreservesFiniteLimits (preimageFunctor f) := by
  infer_instance

theorem image_inf_preimage (V : Y.Opens) (U : X.Opens) :
    f ''ᵁ (V ⊓ f ⁻¹ᵁ U) = (f ''ᵁ V) ⊓ U := by
  apply TopologicalSpace.Opens.ext
  exact Set.image_inter_preimage (f : Y → X) (V : Set Y) (U : Set X)

variable (P : Presheaf.MixedCechPresheaf.Presheaves R X)

def coefficientsIso :
    Presheaf.MixedCechPresheaf.intersectionCoefficients R X P ⋙ restrictionFunctor R f ≅
      (preimageFunctor f).op ⋙ Presheaf.MixedCechPresheaf.intersectionCoefficients R Y ((restrictionFunctor R f).obj P) :=
  NatIso.ofComponents (fun U => NatIso.ofComponents (fun V => P.mapIso
    (eqToIso (congrArg op (image_inf_preimage f V.unop U.unop).symm))) (by
      intro V W g
      change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
      exact (P.map_comp _ _).symm.trans
        ((congrArg P.map (Subsingleton.elim _ _)).trans (P.map_comp _ _)))) (by
    intro U V g
    apply NatTrans.ext
    funext Z
    change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
    exact (P.map_comp _ _).symm.trans
      ((congrArg P.map (Subsingleton.elim _ _)).trans (P.map_comp _ _)))

variable {ι : Type u} (U : ι → X.Opens)

/-- The global Čech complex restricts to the Čech complex of the restricted family. -/
def complexIso :
    ((restrictionFunctor R f).mapHomologicalComplex (ComplexShape.up ℕ)).obj (Presheaf.MixedCechPresheaf.complex R X U P) ≅
      Presheaf.MixedCechPresheaf.complex R Y (fun i => f ⁻¹ᵁ U i) ((restrictionFunctor R f).obj P) :=
  Cech.CoefficientChange.CechCoefficientChange.complexIso (restrictionFunctor R f) (FormalCoproduct.mk ι U).cech
    (Presheaf.MixedCechPresheaf.intersectionCoefficients R X P) ≪≫
      (cechComplexFunctor U).mapIso (coefficientsIso R f P) ≪≫
        Cech.BaseChange.CechBaseChange.complexIso (preimageFunctor f) U
          (Presheaf.MixedCechPresheaf.intersectionCoefficients R Y ((restrictionFunctor R f).obj P))

/-- The restriction of the global Čech complex to a family member contracts onto its coefficients. -/
def coverMemberHomotopyEquiv (i : ι) :=
  (PresheafContraction.MixedCechPresheafContraction.localHomotopyEquiv R X U P i).trans
    (HomotopyEquiv.ofIso (complexIso R (U i).ι P U).symm)

/-- The same contraction after forming sheaves on that family member. -/
def coverMemberSheafHomotopyEquiv (i : ι) :=
  (Presheaf.MixedCechPresheaf.sheafification R (U i).toScheme).mapHomotopyEquiv
    (coverMemberHomotopyEquiv R P U i)

def sheafRestrictionFunctor :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v} R) ⥤
      Sheaf (Opens.grothendieckTopology Y) (ModuleCat.{max u v} R) :=
  f.opensFunctor.sheafPushforwardContinuous (ModuleCat.{max u v} R)
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

instance sheafRestriction_additive : (sheafRestrictionFunctor R f).Additive where
  map_add := rfl

instance sheafRestriction_leftAdjoint : (sheafRestrictionFunctor R f).IsLeftAdjoint :=
  (f.opensFunctor.sheafAdjunctionCocontinuous (ModuleCat.{max u v} R)
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).isLeftAdjoint

instance sheafRestriction_rightAdjoint : (sheafRestrictionFunctor R f).IsRightAdjoint := by
  dsimp [sheafRestrictionFunctor]
  infer_instance

instance sheafRestriction_preservesHomology : (sheafRestrictionFunctor R f).PreservesHomology := by
  infer_instance

/-- Sheafification commutes with restriction to this open subscheme. -/
def sheafificationIso : restrictionFunctor R f ⋙ Presheaf.MixedCechPresheaf.sheafification R Y ≅
    Presheaf.MixedCechPresheaf.sheafification R X ⋙ sheafRestrictionFunctor R f :=
  f.opensFunctor.pushforwardContinuousSheafificationCompatibility (ModuleCat.{max u v} R)
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

def sheafificationComplexIso :
    ((restrictionFunctor R f ⋙ Presheaf.MixedCechPresheaf.sheafification R Y).mapHomologicalComplex (ComplexShape.up ℕ)) ≅
      ((Presheaf.MixedCechPresheaf.sheafification R X ⋙ sheafRestrictionFunctor R f).mapHomologicalComplex (ComplexShape.up ℕ)) where
  hom := (sheafificationIso R f).hom.mapHomologicalComplex (ComplexShape.up ℕ)
  inv := (sheafificationIso R f).inv.mapHomologicalComplex (ComplexShape.up ℕ)
  hom_inv_id := by
    apply NatTrans.ext
    funext K
    ext n : 1
    exact (sheafificationIso R f).hom_inv_id_app (K.X n)
  inv_hom_id := by
    apply NatTrans.ext
    funext K
    ext n : 1
    exact (sheafificationIso R f).inv_hom_id_app (K.X n)

/-- The actual global Čech sheaf complex restricts to the local Čech sheaf complex. -/
def sheafComplexIso :
    ((sheafRestrictionFunctor R f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (Presheaf.MixedCechPresheaf.sheafComplex R X U P) ≅
        Presheaf.MixedCechPresheaf.sheafComplex R Y (fun i => f ⁻¹ᵁ U i) ((restrictionFunctor R f).obj P) :=
  ((sheafificationComplexIso R f).app
    (Presheaf.MixedCechPresheaf.complex R X U P)).symm ≪≫
      ((Presheaf.MixedCechPresheaf.sheafification R Y).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso (complexIso R f P U)

/-- Restrictions of the global sheaf complex have the proved local contractions. -/
def restrictedSheafHomotopyEquiv (i : ι) :=
  (PresheafContraction.MixedCechPresheafContraction.localSheafHomotopyEquiv R X U P i).trans
    (HomotopyEquiv.ofIso (sheafComplexIso R (U i).ι P U).symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.CechRestriction.MixedCechRestriction
