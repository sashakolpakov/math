import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso

/-! # Cone Total Map Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConeTotalMapCoordinates

noncomputable section

/-! The cone-compatible total map is the original Cech total map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v s t
variable (R : Type u) [CommRing R] {C : Type s} [Category.{t} C] [HasBinaryProducts C]
  {ι : Type} (U : ι → C)
  {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ℕ} (a : K ⟶ L)

theorem map : GeometricComparison.CechPresheaf.ConeNaturality.CechPresheafConeNaturality.totalMap U a =
    AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.map R (NonemptyCechNerve.nerve U) a := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConeTotalMapCoordinates
