import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELTransport

/-! # Action Family Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family

noncomputable section

/-! Compare the native positively polarized action datum with the PEL
isogeny interface, including its actual pullback rather than a replacement datum. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
variable {g N : ℕ} {δ : Fin g → ℕ} {S T : Scheme}

abbrev actionFamily (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N S) :
    AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S :=
  AbelianScheme.TateComparison.PEL.PELFamilyData.ofPolarized A.polarized (AbelianScheme.TateComparison.PELAdapters.actionToEnd A.action)

def actionIsoToFamilyIso {A B : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N S}
    (e : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso A B) : AbelianScheme.TateComparison.PELModuli.PELFamilyIso (actionFamily A) (actionFamily B) where
  abelian := e.polarized.abelian
  dual := e.polarized.dual
  abelianGroup := e.polarized.abelianGroup
  dualGroup := e.polarized.dualGroup
  polarization := e.polarized.polarization
  poincare := e.polarized.poincare
  marking := e.polarized.level
  equivariant a := by
    change AbelianScheme.TateComparison.End.endSchemeMap A.polarized.abelian.scheme ((AbelianScheme.TateComparison.PELAdapters.actionToEnd A.action) a) ≫
        e.polarized.abelian.hom =
      e.polarized.abelian.hom ≫ AbelianScheme.TateComparison.End.endSchemeMap B.polarized.abelian.scheme ((AbelianScheme.TateComparison.PELAdapters.actionToEnd B.action) a)
    rw [AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap, AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap]
    exact e.action a

def familyIsoToActionIso {A B : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N S}
    (e : AbelianScheme.TateComparison.PELModuli.PELFamilyIso (actionFamily A) (actionFamily B)) : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso A B where
  polarized := {
    abelian := e.abelian
    dual := e.dual
    abelianGroup := e.abelianGroup
    dualGroup := e.dualGroup
    polarization := e.polarization
    poincare := e.poincare
    level := e.marking }
  action a := by
    have h := e.equivariant a
    change AbelianScheme.TateComparison.End.endSchemeMap A.polarized.abelian.scheme ((AbelianScheme.TateComparison.PELAdapters.actionToEnd A.action) a) ≫
        e.abelian.hom =
      e.abelian.hom ≫ AbelianScheme.TateComparison.End.endSchemeMap B.polarized.abelian.scheme ((AbelianScheme.TateComparison.PELAdapters.actionToEnd B.action) a) at h
    rw [AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap, AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap] at h
    exact h

/-- The identity maps identify the two native descriptions of the same
base-changed family. Action compatibility is the actual pullback equation. -/
def actionFamilyPullbackIso (A : PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N S) (s : T ⟶ S) :
    AbelianScheme.TateComparison.PELModuli.PELFamilyIso ((actionFamily A).pullback s) (actionFamily (A.pullback s)) where
  abelian := Iso.refl _
  dual := Iso.refl _
  abelianGroup := inferInstanceAs (IsMonHom (𝟙 ((actionFamily A).pullback s).abelian.scheme))
  dualGroup := inferInstanceAs (IsMonHom (𝟙 ((actionFamily A).pullback s).dual.abelian.scheme))
  polarization := (AbelianScheme.TateComparison.PELModuli.PELFamilyIso.refl ((actionFamily A).pullback s)).polarization
  poincare := (AbelianScheme.TateComparison.PELModuli.PELFamilyIso.refl ((actionFamily A).pullback s)).poincare
  marking := (AbelianScheme.TateComparison.PELModuli.PELFamilyIso.refl ((actionFamily A).pullback s)).marking
  equivariant a := by
    change AbelianScheme.TateComparison.End.endSchemeMap _ (((actionFamily A).pullback s).action a) ≫ 𝟙 _ =
      𝟙 _ ≫ AbelianScheme.TateComparison.End.endSchemeMap _ ((AbelianScheme.TateComparison.PELAdapters.actionToEnd (A.action.pullback s)) a)
    rw [Category.comp_id, Category.id_comp, (actionFamily A).pullback_action_schemeMap,
      AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap]
    change (Over.pullback s).map (AbelianScheme.TateComparison.End.endSchemeMap _ ((AbelianScheme.TateComparison.PELAdapters.actionToEnd A.action) a)) =
      (Over.pullback s).map (A.action.map a)
    rw [AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family
