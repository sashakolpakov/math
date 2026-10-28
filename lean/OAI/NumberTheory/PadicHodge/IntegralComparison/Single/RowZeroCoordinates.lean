import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.ShiftZeroCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.AbelianSingleRowTotal

/-! # Row Zero Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Single.RowZeroCoordinates

noncomputable section

/-! The original single-row total comparison has its literal
degree-zero cycle coordinate. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem zero_map {K L : CochainComplex C ℕ} (f : K ⟶ L) :
    homologyMap f 0 ≫ (CochainComplex.isoHomologyπ₀ L).inv ≫ L.iCycles 0 =
      (CochainComplex.isoHomologyπ₀ K).inv ≫ K.iCycles 0 ≫ f.f 0 := by
  rw [← Category.assoc, CochainComplex.isoHomologyπ₀_inv_naturality,
    Category.assoc, cyclesMap_i]

variable [HasCoproducts.{0} C]
  (B : HomologicalComplex₂ C (.up ℕ) (.up ℕ))
  (c : ℕ) (hB : ∀ p q, q ≠ c → IsZero ((B.X p).X q))

theorem coordinate :
    (B.total (.up ℕ)).homologyπ (0 + c) ≫
        (AbelianSingleRowTotal.homologyIso B c hB 0).hom ≫
          (CochainComplex.isoHomologyπ₀ (B.flip.X c)).inv ≫ (B.flip.X c).iCycles 0 =
      (B.total (.up ℕ)).iCycles (0 + c) ≫
        AbelianSingleRowTotal.projection B 0 c (0 + c) rfl := by
  let : (B.total (.up ℕ)).IsStrictlySupported (CohomologyConcentration.shift c) :=
    AbelianSingleRowTotal.supported B c hB
  let K := B.total (.up ℕ)
  let r := AbelianSingleRowTotal.restrictionIso B c hB
  have hz := zero_map r.inv
  have hs := Supported.ShiftZeroCoordinates.zero_coordinate K c
  change K.homologyπ (0 + c) ≫
    ((RowTotalNaturality.supportedIso K c 0).hom ≫ homologyMap r.inv 0) ≫
      (CochainComplex.isoHomologyπ₀ (B.flip.X c)).inv ≫ (B.flip.X c).iCycles 0 = _
  calc
    _ = (K.homologyπ (0 + c) ≫ (RowTotalNaturality.supportedIso K c 0).hom ≫
        (CochainComplex.isoHomologyπ₀ (K.restriction (CohomologyConcentration.shift c))).inv ≫
          (K.restriction (CohomologyConcentration.shift c)).iCycles 0) ≫ r.inv.f 0 := by
      simpa only [Category.assoc] using congrArg (fun a =>
        K.homologyπ (0 + c) ≫ (RowTotalNaturality.supportedIso K c 0).hom ≫ a) hz
    _ = _ := congrArg (fun a => a ≫ r.inv.f 0) hs

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Single.RowZeroCoordinates
