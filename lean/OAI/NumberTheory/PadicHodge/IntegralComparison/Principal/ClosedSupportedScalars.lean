import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechLinear
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.PresheafTrace

/-! # Closed Supported Scalars -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedSupportedScalars

noncomputable section

/-! Closed-scheme coefficient diagrams enter the original supported
single-degree total without changing its degree or signs. Their scalar
maps act by the original ambient scalar after restriction. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X Z : Scheme.{u}} (i : X ⟶ Z) (U : Z.Opens)
private abbrev ambientRing := Γ(Z, U)
private abbrev closedRing := Γ(X, i ⁻¹ᵁ U)
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedSupportedScalars.ambientRing U
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedSupportedScalars.closedRing i U
local notation "C" => (OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf.Index U)ᵒᵖ

def restriction : (C ⥤ ModuleCat.{u} Q) ⥤ (C ⥤ ModuleCat.{u} A) :=
  (Functor.whiskeringRight C (ModuleCat.{u} Q) (ModuleCat.{u} A)).obj
    (ModuleCat.restrictScalars (i.app U).hom)

instance restriction_additive : (restriction i U).Additive := by
  dsimp only [restriction]
  infer_instance

local instance singleLinear (c : ℕ) :
    (single (C ⥤ ModuleCat.{u} A) (.up ℕ) c).Linear A where
  map_smul f r := by
    apply from_single_hom_ext
    simp only [single_map_f_self, smul_f_apply, Linear.comp_smul, Linear.smul_comp]

variable {ι : Type u} [LinearOrder ι] (W : ι → SectionPresheaf.Index U) (c q : ℕ)

def functor : (C ⥤ ModuleCat.{u} Q) ⥤ ModuleCat.{u} A :=
  restriction i U ⋙ single (C ⥤ ModuleCat.{u} A) (.up ℕ) c ⋙
    Supported.CechHomotopyEquivalence.functor W q

instance functor_additive : (functor i U W c q).Additive := by
  dsimp only [functor]
  infer_instance

def additive : (C ⥤ ModuleCat.{u} Q) ⥤ AddCommGrpCat.{u} :=
  functor i U W c q ⋙ forget₂ (ModuleCat.{u} A) AddCommGrpCat

instance additive_additive : (additive i U W c q).Additive := by
  dsimp only [additive]
  infer_instance

theorem restriction_scalar (P : C ⥤ ModuleCat.{u} Q) (a : A) :
    (restriction i U).map (FiniteEtale.PresheafTrace.scalar Q P (i.app U a)) =
      a • 𝟙 ((restriction i U).obj P) := by
  apply NatTrans.ext
  funext r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem scalar_map (P : C ⥤ ModuleCat.{u} Q) (a : A)
    (y : (functor i U W c q).obj P) :
    (functor i U W c q).map (FiniteEtale.PresheafTrace.scalar Q P (i.app U a)) y =
      a • y := by
  change (Supported.CechHomotopyEquivalence.functor W q).map
    ((single (C ⥤ ModuleCat.{u} A) (.up ℕ) c).map
      ((restriction i U).map (FiniteEtale.PresheafTrace.scalar Q P (i.app U a)))) y = _
  rw [restriction_scalar, Functor.map_smul, CategoryTheory.Functor.map_id,
    Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedSupportedScalars
