import OAI.AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient

/-! # Coefficient Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientChange

noncomputable section

/-! Actual principal-open coefficients and their inclusion maps under a
ring homomorphism. The index category is retained for diagram transport. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory
universe u v
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

def functor (f : A →+* B) : AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object A ⥤ AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object B where
  obj r := ⟨f r.val⟩
  map {r s} h := homOfLE (by
    intro q hq
    exact leOfHom h (show PrimeSpectrum.comap f q ∈ PrimeSpectrum.basicOpen r.val from hq))

theorem functor_obj_val (f : A →+* B) (r : AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object A) :
    ((functor f).obj r).val = f r.val := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.CoefficientChange
