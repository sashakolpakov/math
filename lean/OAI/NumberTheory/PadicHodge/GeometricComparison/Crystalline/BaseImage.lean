import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

/-! # Base Image -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.BaseImage.CrystallineBaseImage

noncomputable section

/-! A morphism of original crystalline objects preserves their image in the base scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
  {U V : IntegralComparison.BigCrystallineSite.Object p B J δ f} (α : U ⟶ V)

include α in
theorem range_subset : Set.range U.mapToX ⊆ Set.range V.mapToX := by
  rintro _ ⟨x, rfl⟩
  exact ⟨IntegralComparison.BigCrystallineSite.Object.closed.map α x, congrArg (fun m => m x) α.overX⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.BaseImage.CrystallineBaseImage
