import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.Leibniz

/-! # Wedge Algebra -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.WedgeAlgebra

noncomputable section

/-! Associativity and the closed unit for the native de Rham wedge
product, retaining the original differential-symbol modules. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra ℚ A]

theorem wedge_assoc {p q r : ℕ} (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) (z : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A r) :
    Wedge.degreeCast R A (Nat.add_assoc p q r) (Wedge.wedge R A (p + q) r (Wedge.wedge R A p q x y) z) =
      Wedge.wedge R A p (q + r) x (Wedge.wedge R A q r y z) := by
  apply Values.Wedge.value_injective R A (p + (q + r))
  simp only [Values.Wedge.value_degreeCast, Values.Wedge.value_wedge, mul_assoc]

def unitForm : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 0 := AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 (fun i => i.elim0)

theorem value_unit : Values.Wedge.value R A 0 (unitForm R A) = 1 := by
  rw [unitForm, Values.Wedge.value_symbol, one_smul]
  exact ExteriorAlgebra.ιMulti_zero_apply _

theorem unit_wedge {p : ℕ} (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) :
    Wedge.degreeCast R A (Nat.zero_add p) (Wedge.wedge R A 0 p (unitForm R A) x) = x := by
  apply Values.Wedge.value_injective R A p
  rw [Values.Wedge.value_degreeCast, Values.Wedge.value_wedge, value_unit, one_mul]

theorem wedge_unit {p : ℕ} (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) : Wedge.wedge R A p 0 x (unitForm R A) = x := by
  apply Values.Wedge.value_injective R A p
  exact (Values.Wedge.value_wedge R A p 0 x (unitForm R A)).trans (by rw [value_unit, mul_one])

theorem differential_unit : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A 0 (unitForm R A) = 0 := by
  apply Values.Wedge.value_injective R A 1
  change Values.Wedge.differentialValue R A 0 (unitForm R A) = Values.Wedge.value R A 1 0
  rw [unitForm, Values.Wedge.differentialValue_symbol, Derivation.map_one_eq_zero, map_zero, zero_mul, map_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.WedgeAlgebra
