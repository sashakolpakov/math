import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.RefinedHomotopy

/-! # One Homotopy Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.OneHomotopySquare.CechPresheafHOneHomotopySquare

noncomputable section

/-! The homotopy square in the original presheaf Cech H-one
coordinates is stated using the same typed H-one map interface. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v s t
variable (R : Type u) [CommRing R] {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {ι : Type} (U : ι → C)
  {K₂ K₁ L₂ L₁ : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ}
  (a : K₂ ⟶ L₂) (b : L₂ ⟶ L₁) (c : K₂ ⟶ K₁) (d : K₁ ⟶ L₁)
  (h : Homotopy (a ≫ b) (c ≫ d))

include h in
theorem homology : RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne R U a ≫
    RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne R U b =
      RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne R U c ≫ RefinedHomotopy.CechPresheafRefinedHomotopy.mapHOne R U d :=
  Cech.TotalHomotopySquare.CechTotalHomotopySquare.homology R (IntegralComparison.NonemptyCechNerve.nerve U) a b c d h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.OneHomotopySquare.CechPresheafHOneHomotopySquare
