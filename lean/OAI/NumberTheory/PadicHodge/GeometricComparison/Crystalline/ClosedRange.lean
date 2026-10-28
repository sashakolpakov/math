import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ClosedTopology

/-! # Closed Range -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.ClosedRange.CrystallineClosedRange

noncomputable section

/-! The closed schemes detect containment of ambient images for original
nilpotent crystalline objects. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
  {U V T : IntegralComparison.BigCrystallineSite.Object p B J δ f} (α : U ⟶ V) (β : T ⟶ V)

theorem closed_range (hV : Function.Injective V.mapToX)
    (h : Set.range T.mapToX ⊆ Set.range U.mapToX) :
    Set.range (IntegralComparison.BigCrystallineSite.Object.closed.map β) ⊆ Set.range (IntegralComparison.BigCrystallineSite.Object.closed.map α) := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := h ⟨y, rfl⟩
  refine ⟨z, hV ?_⟩
  have hα : V.mapToX (IntegralComparison.BigCrystallineSite.Object.closed.map α z) = U.mapToX z :=
    congrArg (fun m => m z) α.overX
  have hβ : V.mapToX (IntegralComparison.BigCrystallineSite.Object.closed.map β y) = T.mapToX y :=
    congrArg (fun m => m y) β.overX
  exact hα.trans (hz.trans hβ.symm)

theorem ambient_range (h : Set.range (IntegralComparison.BigCrystallineSite.Object.closed.map β) ⊆ Set.range (IntegralComparison.BigCrystallineSite.Object.closed.map α)) :
    Set.range (IntegralComparison.BigCrystallineSite.Object.ambient.map β) ⊆ Set.range (IntegralComparison.BigCrystallineSite.Object.ambient.map α) := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, rfl⟩ := IntegralComparison.Crystalline.ClosedTopology.quotientSpec_surjective T x
  obtain ⟨z, hz⟩ := h ⟨y, rfl⟩
  refine ⟨IntegralComparison.BigCrystallineSite.Object.closedImmersion.app U z, ?_⟩
  have hα : IntegralComparison.BigCrystallineSite.Object.ambient.map α (IntegralComparison.BigCrystallineSite.Object.closedImmersion.app U z) =
      IntegralComparison.BigCrystallineSite.Object.closedImmersion.app V (IntegralComparison.BigCrystallineSite.Object.closed.map α z) :=
    congrArg (fun m => m z) (IntegralComparison.BigCrystallineSite.Object.closedImmersion.naturality α).symm
  have hβ : IntegralComparison.BigCrystallineSite.Object.ambient.map β (IntegralComparison.BigCrystallineSite.Object.closedImmersion.app T y) =
      IntegralComparison.BigCrystallineSite.Object.closedImmersion.app V (IntegralComparison.BigCrystallineSite.Object.closed.map β y) :=
    congrArg (fun m => m y) (IntegralComparison.BigCrystallineSite.Object.closedImmersion.naturality β).symm
  exact hα.trans ((congrArg (IntegralComparison.BigCrystallineSite.Object.closedImmersion.app V) hz).trans hβ.symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.ClosedRange.CrystallineClosedRange
