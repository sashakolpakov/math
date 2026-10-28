import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.RowTotalNaturality

/-! # Shift Zero Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.ShiftZeroCoordinates

noncomputable section

/-! The original supported-degree homology shift preserves the actual
cycle coordinate in its lowest degree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
open OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration OAI.NumberTheory.PadicHodge.IntegralComparison.Single.RowTotalNaturality
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : CochainComplex C ℕ) (c : ℕ) [K.IsStrictlySupported (CohomologyConcentration.shift c)]

local instance : IsIso (K.restrictionToTruncGE' (CohomologyConcentration.shift c)) :=
  HomologicalComplex.Hom.isIso_of_components _

def cyclesCoordinate (n : ℕ) : K.cycles (n + c) ⟶ (K.restriction (CohomologyConcentration.shift c)).cycles n :=
  cyclesMap (K.πTruncGE (CohomologyConcentration.shift c)) (n + c) ≫
    ((K.truncGE' (CohomologyConcentration.shift c)).extendCyclesIso (CohomologyConcentration.shift c) (show (CohomologyConcentration.shift c).f n = n + c from rfl)).hom ≫
      cyclesMap (inv (K.restrictionToTruncGE' (CohomologyConcentration.shift c))) n

theorem homologyπ_coordinate (n : ℕ) :
    K.homologyπ (n + c) ≫ (Single.RowTotalNaturality.supportedIso K c n).hom =
      cyclesCoordinate K c n ≫ (K.restriction (CohomologyConcentration.shift c)).homologyπ n := by
  simp only [Single.RowTotalNaturality.supportedIso, Iso.trans_hom, Iso.symm_hom, homologyMapIso_hom,
    homologyMapIso_inv, asIso_hom, asIso_inv, cyclesCoordinate, Category.assoc]
  erw [homologyπ_naturality_assoc, homologyπ_extendHomologyIso_hom_assoc,
    homologyπ_naturality]

theorem cyclesCoordinate_i (n : ℕ) :
    cyclesCoordinate K c n ≫ (K.restriction (CohomologyConcentration.shift c)).iCycles n =
      K.iCycles (n + c) := by
  let e := (K.truncGE' (CohomologyConcentration.shift c)).extendXIso (CohomologyConcentration.shift c)
    (show (CohomologyConcentration.shift c).f n = n + c from rfl)
  let r := K.restrictionToTruncGE' (CohomologyConcentration.shift c)
  have h₁ := cyclesMap_i (inv r) n
  have h₂ := (K.truncGE' (CohomologyConcentration.shift c)).extendCyclesIso_hom_iCycles (CohomologyConcentration.shift c)
    (show (CohomologyConcentration.shift c).f n = n + c from rfl)
  have h₃ := cyclesMap_i (K.πTruncGE (CohomologyConcentration.shift c)) (n + c)
  have hp : (K.πTruncGE (CohomologyConcentration.shift c)).f (n + c) = r.f n ≫ e.inv := by
    exact ((CohomologyConcentration.shift c).liftExtend_f r (K.restrictionToTruncGE'_hasLift (CohomologyConcentration.shift c))
      (show (CohomologyConcentration.shift c).f n = n + c from rfl)).trans (Category.id_comp (r.f n ≫ e.inv))
  have hr : r.f n ≫ (inv r).f n = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, IsIso.hom_inv_id, HomologicalComplex.id_f]
  have hx : (K.πTruncGE (CohomologyConcentration.shift c)).f (n + c) ≫ e.hom ≫ (inv r).f n = 𝟙 _ := by
    rw [hp, Category.assoc, Iso.inv_hom_id_assoc, hr]
    rfl
  calc
    _ = cyclesMap (K.πTruncGE (CohomologyConcentration.shift c)) (n + c) ≫
        ((K.truncGE' (CohomologyConcentration.shift c)).extendCyclesIso (CohomologyConcentration.shift c)
          (show (CohomologyConcentration.shift c).f n = n + c from rfl)).hom ≫
        (K.truncGE' (CohomologyConcentration.shift c)).iCycles n ≫ (inv r).f n := by
      simpa only [cyclesCoordinate, r, Category.assoc] using congrArg (fun a =>
        cyclesMap (K.πTruncGE (CohomologyConcentration.shift c)) (n + c) ≫
          ((K.truncGE' (CohomologyConcentration.shift c)).extendCyclesIso (CohomologyConcentration.shift c)
            (show (CohomologyConcentration.shift c).f n = n + c from rfl)).hom ≫ a) h₁
    _ = cyclesMap (K.πTruncGE (CohomologyConcentration.shift c)) (n + c) ≫
        (K.truncGE (CohomologyConcentration.shift c)).iCycles (n + c) ≫ e.hom ≫ (inv r).f n := by
      simpa only [e, truncGE, Category.assoc] using congrArg (fun a =>
        cyclesMap (K.πTruncGE (CohomologyConcentration.shift c)) (n + c) ≫ a ≫ (inv r).f n) h₂
    _ = K.iCycles (n + c) ≫ (K.πTruncGE (CohomologyConcentration.shift c)).f (n + c) ≫
        e.hom ≫ (inv r).f n := by
      simpa only [e, truncGE, Category.assoc] using congrArg (fun a => a ≫ e.hom ≫ (inv r).f n) h₃
    _ = _ := by rw [hx, Category.comp_id]

theorem zero_coordinate :
    K.homologyπ (0 + c) ≫ (Single.RowTotalNaturality.supportedIso K c 0).hom ≫
        (CochainComplex.isoHomologyπ₀ (K.restriction (CohomologyConcentration.shift c))).inv ≫
          (K.restriction (CohomologyConcentration.shift c)).iCycles 0 = K.iCycles (0 + c) := by
  rw [← Category.assoc, ← Category.assoc, homologyπ_coordinate]
  simpa only [Category.assoc, HomologicalComplex.isoHomologyπ_hom_inv_id_assoc] using
    cyclesCoordinate_i K c 0

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.ShiftZeroCoordinates
