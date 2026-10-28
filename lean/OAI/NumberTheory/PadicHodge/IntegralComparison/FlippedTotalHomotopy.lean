import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.TotalHomotopy

/-! # Flipped Total Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FlippedTotalHomotopy

noncomputable section

/-! A genuine homotopy of bicomplex maps gives equality on the
original signed totals with the coefficient degree first. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {R : Type u} [CommRing R]
  {K L : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)}
  {f g : K ⟶ L} (h : Homotopy f g)

local instance total (K : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)) :
    K.HasTotal (.up ℕ) := AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

include h in
theorem homology (i : ℕ) :
    HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map (GeometricComparison.TotalFlip.TotalFlipNaturality.flipped f) (.up ℕ)) i =
    HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map (GeometricComparison.TotalFlip.TotalFlipNaturality.flipped g) (.up ℕ)) i := by
  apply (cancel_mono (HomologicalComplex.homologyMap (L.totalFlipIso (.up ℕ)).hom i)).mp
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    GeometricComparison.TotalFlip.TotalFlipNaturality.natural, GeometricComparison.TotalFlip.TotalFlipNaturality.natural,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    AlgebraicGeometry.Crystalline.Cohomology.Module.TotalHomotopy.ModuleTotalHomotopy.homology h i]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FlippedTotalHomotopy
