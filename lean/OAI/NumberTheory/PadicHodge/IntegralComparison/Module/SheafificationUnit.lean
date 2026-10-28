import OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafificationScalars

/-! # Sheafification Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafificationUnit

noncomputable section

/-! Base scalar restriction detects isomorphisms in the canonical module sheafification unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [CommRing k] (X : Over (Spec (CommRingCat.of k)))
  (M : PresheafOfModules.{u} X.left.ringCatSheaf.obj) (U : X.left.Opensᵒᵖ)

def unit : M.obj U ⟶ ((SchemeModuleSheafification.functor X.left).obj M).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.left.ringCatSheaf.obj)).unit.app M).app U

theorem scalar_isIso_iff :
    IsIso ((toSheafify (Opens.grothendieckTopology X.left)
      ((AlgebraSheafScalars.presheaves k X).obj M)).app U) ↔ IsIso (SheafificationUnit.unit k X M U) := by
  let P := (AlgebraSheafScalars.presheaves k X).obj M
  let a := (AlgebraSheafificationScalars.map k X M).hom.app U
  have : IsIso a := inferInstance
  have h : (toSheafify (Opens.grothendieckTopology X.left) P).app U ≫ a =
      (AlgebraSheafificationScalars.unit k X M).app U :=
    congrArg (fun f => f.app U) (AlgebraSheafificationScalars.map_fac k X M)
  constructor
  · intro hu
    let : IsIso ((toSheafify (Opens.grothendieckTopology X.left) P).app U) := hu
    have hs : IsIso ((AlgebraSheafificationScalars.unit k X M).app U) := by
      rw [← h]
      infer_instance
    rw [ConcreteCategory.isIso_iff_bijective] at hs ⊢
    exact hs
  · intro hu
    have hs : IsIso ((AlgebraSheafificationScalars.unit k X M).app U) := by
      rw [ConcreteCategory.isIso_iff_bijective] at hu ⊢
      exact hu
    have : IsIso ((toSheafify (Opens.grothendieckTopology X.left) P).app U ≫ a) := h.symm ▸ hs
    exact IsIso.of_isIso_comp_right _ a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafificationUnit
