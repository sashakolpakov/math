import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PresheafContraction
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.Pullback

/-! # Cover -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction

noncomputable section

/-!
# Restricting the global Čech presheaf complex

The restriction of the global complex to an open subscheme is identified
with the complex of the inverse-image family. This connects the global
construction to the proved local contractions.
-/

open _root_.CategoryTheory Limits Opposite _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

def restrictionFunctor : Presheaf.CechPresheaf.Presheaves R X ⥤ Presheaf.CechPresheaf.Presheaves R Y :=
  (Functor.whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ (ModuleCat.{u} R)).obj f.opensFunctor.op

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

variable (P : Presheaf.CechPresheaf.Presheaves R X)

def coefficientsIso :
    Presheaf.CechPresheaf.intersectionCoefficients R X P ⋙ restrictionFunctor R f ≅
      (preimageFunctor f).op ⋙ Presheaf.CechPresheaf.intersectionCoefficients R Y ((restrictionFunctor R f).obj P) :=
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
    ((restrictionFunctor R f).mapHomologicalComplex (ComplexShape.up ℕ)).obj (Presheaf.CechPresheaf.complex R X U P) ≅
      Presheaf.CechPresheaf.complex R Y (fun i => f ⁻¹ᵁ U i) ((restrictionFunctor R f).obj P) :=
  CoefficientChange.CechCoefficientChange.complexIso (restrictionFunctor R f) (FormalCoproduct.mk ι U).cech
    (Presheaf.CechPresheaf.intersectionCoefficients R X P) ≪≫
      (cechComplexFunctor U).mapIso (coefficientsIso R f P) ≪≫
        BaseChange.CechBaseChange.complexIso (preimageFunctor f) U
          (Presheaf.CechPresheaf.intersectionCoefficients R Y ((restrictionFunctor R f).obj P))

/-- The restriction of the global Čech complex to a family member contracts onto its coefficients. -/
def coverMemberHomotopyEquiv (i : ι) :=
  (PresheafContraction.CechPresheafContraction.localHomotopyEquiv R X U P i).trans
    (HomotopyEquiv.ofIso (complexIso R (U i).ι P U).symm)

/-- The same contraction after forming sheaves on that family member. -/
def coverMemberSheafHomotopyEquiv (i : ι) :=
  (Presheaf.CechPresheaf.sheafification R (U i).toScheme).mapHomotopyEquiv
    (coverMemberHomotopyEquiv R P U i)

def sheafRestrictionFunctor :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⥤
      Sheaf (Opens.grothendieckTopology Y) (ModuleCat.{u} R) :=
  f.opensFunctor.sheafPushforwardContinuous (ModuleCat.{u} R)
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

instance sheafRestriction_additive : (sheafRestrictionFunctor R f).Additive where
  map_add := rfl

instance sheafRestriction_leftAdjoint : (sheafRestrictionFunctor R f).IsLeftAdjoint :=
  (f.opensFunctor.sheafAdjunctionCocontinuous (ModuleCat.{u} R)
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).isLeftAdjoint

instance sheafRestriction_rightAdjoint : (sheafRestrictionFunctor R f).IsRightAdjoint := by
  dsimp [sheafRestrictionFunctor]
  infer_instance

instance sheafRestriction_preservesHomology : (sheafRestrictionFunctor R f).PreservesHomology := by
  infer_instance

/-- Sheafification commutes with restriction to this open subscheme. -/
def sheafificationIso : restrictionFunctor R f ⋙ Presheaf.CechPresheaf.sheafification R Y ≅
    Presheaf.CechPresheaf.sheafification R X ⋙ sheafRestrictionFunctor R f :=
  f.opensFunctor.pushforwardContinuousSheafificationCompatibility (ModuleCat.{u} R)
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

def sheafificationComplexIso :
    ((restrictionFunctor R f ⋙ Presheaf.CechPresheaf.sheafification R Y).mapHomologicalComplex (ComplexShape.up ℕ)) ≅
      ((Presheaf.CechPresheaf.sheafification R X ⋙ sheafRestrictionFunctor R f).mapHomologicalComplex (ComplexShape.up ℕ)) where
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
      (Presheaf.CechPresheaf.sheafComplex R X U P) ≅
        Presheaf.CechPresheaf.sheafComplex R Y (fun i => f ⁻¹ᵁ U i) ((restrictionFunctor R f).obj P) :=
  ((sheafificationComplexIso R f).app
    (Presheaf.CechPresheaf.complex R X U P)).symm ≪≫
      ((Presheaf.CechPresheaf.sheafification R Y).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso (complexIso R f P U)

/-- Restrictions of the global sheaf complex have the proved local contractions. -/
def restrictedSheafHomotopyEquiv (i : ι) :=
  (PresheafContraction.CechPresheafContraction.localSheafHomotopyEquiv R X U P i).trans
    (HomotopyEquiv.ofIso (sheafComplexIso R (U i).ι P U).symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction
